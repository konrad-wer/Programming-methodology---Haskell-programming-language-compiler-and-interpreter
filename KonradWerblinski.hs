-- Wymagamy, by moduł zawierał tylko bezpieczne funkcje
{-# LANGUAGE Safe #-}
-- Definiujemy moduł zawierający rozwiązanie.
-- Należy zmienić nazwę modułu na {Imie}{Nazwisko} gdzie za {Imie}
-- i {Nazwisko} należy podstawić odpowiednio swoje imię i nazwisko
-- zaczynające się wielką literą oraz bez znaków diakrytycznych.
module KonradWerblinski (typecheck, eval) where

-- Importujemy moduły z definicją języka oraz typami potrzebnymi w zadaniu
import AST
import DataTypes
import Data.Either
import qualified Data.Map as Map


-- Funkcja sprawdzająca typy
-- Dla wywołania typecheck vars e zakładamy, że zmienne występujące
-- w vars są już zdefiniowane i mają typ int, i oczekujemy by wyrażenia e
-- miało typ int
  
-----------------Typy------------------------------------
type TypeEnvironment =  Map.Map Var Type
newtype TypeEnvEntry = TypeEnvEntry (Var, Type)
data Error p = UndefindedVariable p | ExpectedInt p | ExpectedBool p | 
               ExpectedList p | ExpectedPair p | ExpectedFunction p |
               IfTypeMismatch p | FunctionResTypeMismatch p | 
               FunctionArgTypeMismatch p | LackingDefinition p | ConsTypeMismatch p |
               MatchTypeMismatch p | WrongTypeAnottation p deriving (Show, Eq)

------------------Środowisko typów-----------------------------------
--Środowisko zaimplementowane za pomocą zwykłej listy
make_initial_type_env :: [(Var, Type)] -> [FunctionDef p] -> TypeEnvironment
make_initial_type_env vars funDefs =
  Map.fromList (map (\f -> (funcName f, TArrow (funcArgType f) (funcResType f))) funDefs ++ vars)

get_type_from_env :: TypeEnvironment -> Expr p -> Either (Error p) Type
get_type_from_env env (EVar p x) = 
  if Map.notMember x env then
    Left $ UndefindedVariable p
  else
	return $ env Map.! x
	
add_to_type_env :: TypeEnvironment -> Var -> Type -> TypeEnvironment 
add_to_type_env env name t = Map.insert name t env

------------------Infer type-------------------------------------
infer_type :: TypeEnvironment -> Expr p -> Either (Error p) Type
infer_type type_env (EVar p x) =  get_type_from_env type_env (EVar p x) --Zmienne
infer_type _ (ENum _ _) = return TInt  --Stała Int
infer_type _ (EBool _ _) = return TBool  --Stała Bool
infer_type _ (EUnit _) = return TUnit -- Stała unit
infer_type _ (ENil p (TList t)) = return $ TList t -- Lista pusta
infer_type _ (ENil p t) = Left $ WrongTypeAnottation p

infer_type type_env (ECons p e1 e2) = do --Konstruktor listy niepustej
  t1 <- infer_type type_env e1
  t2 <- infer_type type_env e2
  if TList t1 == t2 then
    return t2
  else
    Left $ ConsTypeMismatch p
    
infer_type type_env (EPair p e1 e2) = do --Konstruktor pary
  t1 <- infer_type type_env e1
  t2 <- infer_type type_env e2
  return $ TPair t1 t2
  
infer_type type_env (EFst p e) =  do -- Pierwsza projekcja pary
  t <- infer_type type_env e
  case t of
    TPair t1 t2 -> return t1
    _ -> Left $ ExpectedPair p 
    
infer_type type_env (ESnd p e) = do -- Druga projekcja pary
  t <- infer_type type_env e
  case t of
    TPair t1 t2 -> return t2
    _ -> Left $ ExpectedPair p 

infer_type type_env (EApp p e1 e2) = do --Aplikacja funkcji
  t1 <- infer_type type_env e1
  t2 <- infer_type type_env e2
  case t1 of
    TArrow argType resType -> if argType == t2 then return resType else Left $ FunctionArgTypeMismatch p
    _ -> Left $ ExpectedFunction p 
  
infer_type type_env (EFn p arg argType body) = do --Lambda
  resType <- infer_type(add_to_type_env type_env arg argType) body
  return $ TArrow argType resType
       
infer_type type_env (EMatchL p e1 e2 (x, xs, e3)) = do  -- pattern matching
  t1List <- infer_type type_env e1
  case t1List of
    TList t1 -> do
      t2 <- infer_type type_env e2
      t3 <- infer_type (add_to_type_env(add_to_type_env type_env xs t1List) x t1) e3
      if t2 == t3 then
        return t2
      else
        Left $ MatchTypeMismatch p
    _ -> Left $ ExpectedList p

infer_type type_env (EUnary p UNot e) = --negacja
  case infer_type type_env e of
    Right TBool -> Right TBool 
    Right _-> Left $ ExpectedBool p
    Left error -> Left error
  
infer_type type_env (EUnary p UNeg e) = --minus jednoargumentowy
  case infer_type  type_env e of
    Right TInt -> Right TInt
    Right _ -> Left $ ExpectedInt p
    Left error -> Left error
  
infer_type type_env (EBinary p op e1 e2) --operator binarny
  | elem op [BAnd, BOr] = infer_type_logic type_env e1 e2
  | elem op [BEq, BNeq, BLt, BGt, BLe, BGe] = infer_type_arythm_or_comp type_env e1 e2 TBool
  | elem op [BAdd, BSub, BMul, BDiv, BMod] = infer_type_arythm_or_comp type_env e1 e2 TInt

infer_type  type_env (EIf p e1 e2 e3) = do --if
    t1 <- infer_type type_env e1
    t2 <- infer_type type_env e2
    t3 <- infer_type type_env e3
    if t1 /= TBool then
      Left $ ExpectedBool p
    else if t2 == t3 then
      return $ t2
    else
      Left $ IfTypeMismatch p
  
infer_type type_env (ELet p x e1 e2) = do--let
  xtype <- infer_type type_env e1
  infer_type (add_to_type_env type_env x xtype) e2
     
--sprawdzenie typu operatorów porównanie i arytmetycznych, przedostatni argument to wynikowy typ czyli jedyna
--rzecz, która odróżnia te dwie reguły  
infer_type_arythm_or_comp ::  TypeEnvironment -> Expr p -> Expr p -> Type-> Either (Error p) Type 
infer_type_arythm_or_comp type_env e1 e2 expr_type = 
  case (infer_type type_env e1, infer_type type_env e2) of
    (Left error, _) -> Left error 
    (_, Left error) -> Left error
    (Right TInt, Right TInt) -> Right expr_type
    (Right TInt, _) -> Left $ ExpectedInt $ getData e2
    _ -> Left $ ExpectedInt $ getData e1

--sprawdzenie typu operatora porównania    
infer_type_logic :: TypeEnvironment -> Expr p -> Expr p -> Either (Error p) Type
infer_type_logic type_env e1 e2 = 
  case (infer_type type_env e1, infer_type type_env e2) of
    (Left error, _) -> Left error 
    (_, Left error) -> Left error
    (Right TBool, Right TBool) -> Right TBool
    (Right TBool, _) -> Left $ ExpectedBool $ getData e2
    _ -> Left $ ExpectedBool $ getData e1
  
--typecheck głównego wyrażenia programu
typecheck_expr :: [FunctionDef p]-> [Var] -> Expr p -> Either (Error p) Type
typecheck_expr funcList vars = infer_type (make_initial_type_env (zip vars [TInt| n <- [1..]]) funcList)

--typecheck wszystkich funkcji
typecheck_funs :: [FunctionDef p] ->  TypeEnvironment -> Either (Error p) Type
typecheck_funs [] _ = Right TUnit
typecheck_funs (f : fs) type_env =
   infer_type  (add_to_type_env type_env (funcArg f) (funcArgType f)) (funcBody f) >>= 
   (\t -> if t == funcResType f then return t else Left $ FunctionResTypeMismatch (funcPos f)) >>
   typecheck_funs fs type_env

 --główna funkcja eksportowana na zewnątrz modułu    
typecheck :: [FunctionDef p] -> [Var] -> Expr p -> TypeCheckResult p
typecheck funcList vars e = 
  let functions = make_initial_type_env [] funcList in
    case typecheck_funs funcList functions >> typecheck_expr funcList vars e of
      Left (UndefindedVariable p) -> Error p "Undefinded variable"
      Left (ExpectedBool p) -> Error p "Expected bool"
      Left (ExpectedInt p) -> Error p "Expected int"
      Left (ExpectedList p) -> Error p "Expected list in pattern matching"
      Left (ExpectedPair p) -> Error p "Expected pair as an argument of a projection"
      Left (ExpectedFunction p) -> Error p "Expected function in application"
      Left (MatchTypeMismatch p) -> Error p "Mismatched types of expressions in pattern matching"
      Left (IfTypeMismatch p) -> Error p "Mismatched types of expressions e2 and e3 in \"if e1 then e2 else e3\""
      Left (FunctionResTypeMismatch p) -> Error p "Declared and actual function resulst types differ"
      Left (FunctionArgTypeMismatch p) -> Error p "Argunent's type doesn't match the definition of function"
      Left (LackingDefinition p) -> Error p "No definition for function"
      Left (ConsTypeMismatch p) -> Error p "Cons argumets' types don't match"
      Left (WrongTypeAnottation p) -> Error p "Empty list should be of type T list"
      Right TBool -> Error (getData e) "Output must be of type int, found bool"
      Right (TList _) -> Error (getData e) "Output must be of type int, found list"
      Right TUnit -> Error (getData e) "Output must be of type int, found unit"
      Right (TPair _ _) -> Error (getData e) "Output must be of type int, found pair"
      Right (TArrow _ _) -> Error (getData e) "Output must be of type int, found function"
      Right TInt -> Ok
                   

-- Funkcja obliczająca wyrażenia
-- Dla wywołania eval fs input e przyjmujemy, że dla każdej pary (x, v)
-- znajdującej się w input, wartość zmiennej x wynosi v.
-- Możemy założyć, że definicje funckcji fs oraz wyrażenie e są dobrze
-- typowane, tzn. typecheck fs (map fst input) e = Ok

--------------------Typy danych---------------------------------------
data Value = B Bool | I Integer | U | L [Value] | P (Value, Value) | F (Value -> Either String Value)
type EvalEnvironment = Map.Map Var Value

--------------------Środowisko ewaluacji-------------------------------
make_initial_eval_env :: [FunctionDef p] -> [(Var,Integer)] -> EvalEnvironment
make_initial_eval_env funcList vars =
  Map.union (make_function_env funcList) (Map.fromList(map (\(name, val) -> (name, I val)) vars))

get_value_from_env :: EvalEnvironment -> Var -> Value
get_value_from_env env = (env Map.!)

add_to_eval_env :: EvalEnvironment -> Var -> Value -> EvalEnvironment
add_to_eval_env env name value = Map.insert name value env

make_function_env :: [FunctionDef p] -> EvalEnvironment 
make_function_env [] = Map.empty
make_function_env (f : fs) = let self = Map.insert (funcName f) 
                                        (F (\v -> eval_exp (add_to_eval_env self (funcArg f) v)(funcBody f))) 
                                        (_make_function_env self fs) in self

_make_function_env :: EvalEnvironment -> [FunctionDef p] -> EvalEnvironment   
_make_function_env _ [] = Map.empty                        
_make_function_env env (f : fs) = Map.insert (funcName f) 
                                       (F (\v -> eval_exp (add_to_eval_env env (funcArg f) v) (funcBody f)))
                                       (_make_function_env env fs)     

-----------------------Aplikacja operatora binarnego----------------------------------
logic_ops = [(BAnd, (&&)), (BOr, (||))]
comp_ops = [(BEq, (==)), (BNeq, (/=)), (BLt, (<)), (BGt, (>)), (BLe, (<=)), (BGe, (>=))]
arythm_ops = [(BAdd, (+)), (BSub, (-)), (BMul, (*)), (BDiv, div), (BMod, mod)]

op_list_lookup :: [(BinaryOperator, (a -> a -> b))] -> BinaryOperator -> (a -> a -> b)
op_list_lookup ((op1, f) : op_list) op2 = if op1 == op2 then f else op_list_lookup op_list op2

isIand0 :: Value -> Bool
isIand0 (I x) = x == 0
isIand0 _ = False

apply_binary :: BinaryOperator -> Value -> Value -> Either String Value 
apply_binary op v1 v2
  | elem op [BAnd, BOr] = (\op (B x) (B y) -> return $ B (op x y))  (op_list_lookup logic_ops op) v1 v2
  | elem op [BEq, BNeq, BLt, BGt, BLe, BGe] =  (\op (I x) (I y) -> return $ B (op x y) ) (op_list_lookup comp_ops op) v1 v2
  | elem op [BAdd, BSub, BMul, BDiv, BMod] = 
    if ((op == BDiv) || (op == BMod)) && isIand0 v2 then 
      Left $ "DivisionByZero"
    else
      (\op (I x) (I y) -> return $ I (op x y)) (op_list_lookup arythm_ops op) v1 v2
      
------------------------------------eval_exp-------------------------------------------
eval_exp :: EvalEnvironment ->  Expr p -> Either String Value 
eval_exp _ (ENum _ n) = return $ I n   --Stała Int
eval_exp _ (EBool _ b) = return $ B b  --Stała Bool
eval_exp eval_env (EVar _ x) = return $ get_value_from_env eval_env x --Zmienna
eval_exp _ (EUnit _) = return U --Stała Unit
eval_exp _ (ENil  _ _) = return $ L [] --Stala lista pusta

eval_exp eval_env (EFn p arg _ e) =  --Lambda
  return $ F (\val -> eval_exp (add_to_eval_env eval_env arg val) e)

eval_exp eval_env (ECons p e1 e2) = do --Cons
  x <- eval_exp eval_env e1
  L xs <- eval_exp eval_env e2
  return $ L (x : xs)
  
eval_exp eval_env (EPair p e1 e2) = do -- Konstruktor pary
  v1 <- eval_exp eval_env e1
  v2 <- eval_exp eval_env e2
  return $ P (v1, v2)
  
eval_exp eval_env (EFst p e) = do -- Pierwsza projekcja pary
  P (v1, v2) <- eval_exp eval_env e
  return $ v1
  
eval_exp eval_env  (ESnd p e) = do -- Druga projekcja pary
  P (v1, v2) <- eval_exp eval_env e
  return $ v2

eval_exp eval_env (EUnary p UNeg e) = do --minus jednoargumentowy
  I x <- eval_exp eval_env e
  return $ I (-x)

eval_exp eval_env (EUnary p UNot e) = do --negacja
  B x <- eval_exp eval_env e
  return $ B (not x)  
  
eval_exp eval_env (EBinary p op e1 e2) = do --operator binarny
  v1 <- eval_exp eval_env e1
  v2 <- eval_exp eval_env e2
  apply_binary op v1 v2
  
eval_exp eval_env (EIf p e1 e2 e3) = do --if
  B bool_exp <- eval_exp eval_env e1
  if bool_exp then
    eval_exp eval_env e2
  else
    eval_exp eval_env e3
    
eval_exp eval_env (ELet p x e1 e2) = do --let
  x_value <- eval_exp eval_env e1
  eval_exp (add_to_eval_env  eval_env x  x_value)  e2
    
eval_exp eval_env (EApp p e1 e2)  = do -- aplikacja funkcji
  arg <- eval_exp eval_env e2 
  F f <- eval_exp eval_env e1
  f arg
  
eval_exp eval_env (EMatchL p e1 e2 (x, xs, e3)) = do --pattern matching
  list <- eval_exp eval_env e1
  case list of
    L [] -> eval_exp eval_env e2
    L (v : vs) -> eval_exp (add_to_eval_env (add_to_eval_env eval_env x v) xs (L vs)) e3
 
--główna funkcja eksportowana na zewnątrz modułu   
eval :: [FunctionDef p] -> [(Var,Integer)] -> Expr p -> EvalResult
eval fun_List input exp =
  case eval_exp (make_initial_eval_env fun_List input) exp of 
  Right (I value) -> Value value
  Left _ -> RuntimeError  
