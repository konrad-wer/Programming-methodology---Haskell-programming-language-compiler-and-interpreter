{-# LANGUAGE Safe #-}
module KonradWerblinskiCompiler(compile) where

import AST
import MacroAsm
import qualified Data.Map as Map
import Control.Applicative
import Control.Monad

--WERSJA NA PRACOWNIE NR 6

-------------------------------CompState---------------------------------
--stanem jest numer etykiety
--wartością jest wygenerowany kod

newtype CompState t = CompState(Int -> (t, Int))

run :: CompState t -> Int -> (t, Int)
run (CompState f) x = f x

instance Monad CompState where
  return = pure
  f >>= g = CompState(\s -> let (val, s2) = run f s in run (g val) s2)
  
instance Functor CompState where
  fmap = liftM
  
instance Applicative CompState where
  pure x = CompState(\s -> (x, s))
  (<*>) = ap
  
------------------Definicje typów i funkcje pomocnicze--------------------

type Env = Map.Map Var EnvEntry
type FuncTable p = Map.Map Var (FuncTableEntry p)
data EnvEntry = Stack Int | Heap Int 
type FuncTableEntry p = (Int, FunctionDef p)

makeInitialEnv :: [Var] -> Env
makeInitialEnv =  (f 0) . reverse where
  f _ [] = Map.empty
  f n (x : xs) = Map.insert x (Stack n) (f (n + 1) xs)
  
makeFuncTable :: [FunctionDef p] -> FuncTable p
makeFuncTable funs = Map.fromList $ zip (map funcName funs) (zip [0..] funs)   

getFunctionLabel :: FuncTable p -> Var -> Int
getFunctionLabel funTable v = fst (funTable Map.! v)
getFunctionDef :: FuncTable p -> Var -> FunctionDef p
getFunctionDef funTable v = snd (funTable Map.! v)
  
envInsert ::  Var -> EnvEntry -> Env -> Env
envInsert = Map.insert
  
opList = [(BAdd, MAdd), (BSub, MSub), (BMul, MMul),  (BDiv, MDiv), (BMod, MMod), (BAnd, MAnd), (BOr, MOr)]
conList = [(BEq, MC_EQ), (BNeq, MC_NE), (BLt, MC_LT), (BGe, MC_GE), (BLe, MC_LE), (BGt, MC_GT)] 
pairListLookup ((k1, e) : t) k2 = if k1 == k2 then e else pairListLookup t k2

------------------------------------comp----------------------------------

comp :: FuncTable p -> Env -> Int -> Expr p -> [MInstr] -> CompState [MInstr]
comp _ _ _ (ENum p n) code = return (code ++ [MConst n]) --stała Int
comp _ _ _ (EBool p b) code = return (code ++ if b then [MConst (-1)] else [MConst 0]) -- stała bool
comp _ _ _ (EUnit _) code = return (code ++ [MConst 0]) --stała unit
comp funs env stackH (EVar p x) code = -- zmienna
  if  Map.member x env then  --w środowisku przechowywana jest wysokość stosu w chwili włożenia na niego zmiennej, 
    case env Map.! x of  --dzięki temu można się do niej dostać obliczając różnicę obecnej wysokości stosu i wysokości ze środowiska
      Stack v -> return (code ++ [MGetLocal (stackH - v)]) --wartość ze stosu
      Heap v -> return (code ++ [MGetLocal stackH, MGet v]) --wartość z domknięcia
  else
    return (code ++ [MAlloc 1, MPush, MGetLabel(getFunctionLabel funs x), MSet 0, MPopAcc]) --funkcja globalna

--Listy zapisywane sa w pamieci w postaci pary:   (next, val)
comp _ _ _ (ENil _ _) code = return (code ++ [MAlloc 1, MPush, MConst 0, MSet 0, MPopAcc]) --Lista pusta

comp funs env stackH (ECons p e1 e2) code = do --Cons
  code1 <- comp funs env stackH e1 code
  code2 <- comp funs env (stackH + 1) e2 (code1 ++ [MPush])
  return (code2 ++ [MPush, MAlloc 2, MPush, MGetLocal 1, MSet 0, MGetLocal 2, MSet 1, MPopAcc, MPopN 2])

comp funs env stackH (EPair p e1 e2) code = do --Konstruktor pary
  code1 <- comp funs env stackH e1 code
  code2 <- comp funs env (stackH + 1) e2 (code1 ++ [MPush])
  return (code2 ++ [MPush, MAlloc 2, MPush, MGetLocal 1, MSet 1, MGetLocal 2, MSet 0, MPopAcc, MPopN 2])
  
comp funs env stackH (EFst p e) code = do --Pierwsza projekcja pary
  code1 <- comp funs env stackH e code
  return (code1 ++ [MGet 0])
   
comp funs env stackH (ESnd p e) code = do --Druga projekcja pary
  code1 <- comp funs env stackH e code
  return (code1 ++ [MGet 1])

comp funs env stackH (EUnary  p op e) code = do --Operator unarny
  code1 <- comp funs env stackH e code
  if op == UNeg then 
    return (code1 ++ [MNeg])
  else
    return (code1 ++ [MNot])
  
comp funs env stackH (EBinary p op e1 e2) code = do --Operator binarny
  code1 <- comp funs env stackH e1 code 
  code2  <- return (code1 ++ [MPush])
  code3 <- comp funs env (stackH + 1) e2 code2 
  if elem  op [BEq, BNeq, BLt, BGt, BLe, BGe] then 
    CompState(\s -> (code3 ++ 
      [MBranch (pairListLookup conList op) s, 
      MConst 0,
      MJump $ s + 1,
      MLabel s, 
      MConst (-1), 
      MLabel $ s + 1], 
    s + 2))
  else
    return (code3 ++ [(pairListLookup opList op)])
    
comp funs env stackH (EIf p e1 e2 e3) code = do --if
  code1 <- comp funs env stackH e1 code
  whenTrue <- comp funs env stackH e2 []
  whenFalse <- comp funs env stackH e3 []
  CompState(\s -> (code1 ++ 
    [MBranch MC_Z s] ++
    whenTrue ++
    [MJump $ s + 1,
    MLabel s] ++
    whenFalse ++
    [MLabel $ s + 1],
    s + 2))
    
comp funs env stackH (ELet p x e1 e2) code = do --let
  code1 <- comp funs env stackH e1 code
  code2 <- comp funs (envInsert x (Stack (stackH + 1)) env) (stackH + 1) e2 (code1 ++ [MPush])
  return (code2 ++ [MPopN 1])
  

comp funs env stackH (EMatchL p e1 e2 (x, xs, e3)) code = do --pattern matching
  code1 <- comp funs env stackH e1 code
  whenEmpty <- comp funs env stackH e2 []
  whenNotEmpty <- comp funs (envInsert xs (Stack(stackH + 3)) (envInsert x (Stack (stackH + 2)) env)) (stackH + 3) e3 []
  CompState(\s -> (code1 ++
    [MPush,
    MGetLocal 0,
    MGet 0,
    MBranch MC_NZ s,
    MPopN 1] ++ --Pusta
    whenEmpty ++  
    [MJump $ s + 1,
    MLabel $ s, --Niepusta
    MGetLocal 0,
    MGet 1,
    MPush,
    MGetLocal 1,
    MGet 0,
    MPush] ++
    whenNotEmpty ++
    [MPopN 3,
    MLabel $ s + 1],
    s + 2))
	
--konwencja wołania procedur:
--1. włożenie na stos wkaźnika do instacji typu funkcyjnego
--2. włożenie na stos argumentu
--3. wywołanie funkcji, nowa wysokość stosu uwzględnia tylko dwie wyżej wymienione wartości 
--dzięki temu można dostać się do domknięcia w typie funkcyjnym wywołując: MGetLocal stackH
--(wartość jest zwracana w akumulatorze)
--4. zdjęcie argumentu i typu funkcyjnego ze stosu

comp funs env stackH (EApp p e1 e2) code = --Aplikacja funkcji
  if isEVar e1 && let (EVar _ x) = e1 in not (Map.member x env) then
    do --wywołanie funkcji globalnie zadeklarowanej w kodzie bez tworzenia instancji typu funkcyjnego
      code1 <- comp funs env (stackH + 1) e2 (code ++ [MConst 0, MPush]) --dodanie pustego wskaznika na typ funcyjny i obliczenie argumetnu
      return (let (EVar _ x) = e1 in (code1 ++ [MPush, MCall (getFunctionLabel funs x), MPopN 2])) --włożenie argumentu na stos, wywołanie funkcji, czyszczenie stosu
  else
    do  
      code1 <- comp funs env stackH e1 code
      code2 <- comp funs env (stackH + 1) e2 (code1 ++ [MPush])
      return (code2 ++ [MPush, MGetLocal 1, MGet 0, MCallAcc, MPopN 2])
  where 
    isEVar (EVar _ x) = True
    isEVar _ = False
    
comp funs env stackH (EFn p arg _ e) code = --lambda
  let (lambdaEnv, enclosementMakingCode) = makeEnclosement arg (stackH + 1) env in
  do
    lambdaBody <- comp funs (envInsert (arg)(Stack 1) lambdaEnv) 1 e []
    CompState(\s -> (code ++ 
      [MJump $ s + 1, --przeskok nad ciałem lambdy
      MLabel s] ++
      lambdaBody ++ --ciało lambdy w normalnym biegu kodu
      [MRet,
      MLabel $ s + 1, --przeskok nad ciałem lambdy
      MAlloc $ Map.size lambdaEnv + 1, --tworzeie instacji typu funkcyjnego
      MPush,  --w postaci (adres funkcji, [wartości zmiennych w domknięciu])
      MGetLabel s,
      MSet 0] ++
      enclosementMakingCode ++
      [MPopAcc], s + 2))

--tworzenie nowego środwiksa dla domknięcia oraz kodu w assemblerze, który kopiuje wartości środowiska do domnkięcia 	  
makeEnclosement :: Var -> Int -> Env -> (Env, [MInstr]) 
makeEnclosement arg stackH env = let tmp = (make arg stackH (Map.toList env) 1) in (Map.fromList(fst tmp), snd tmp)
  where 
    make _ _ [] _ = ([], [])
    make var stackH ((x, entry) : xs) offset = 
      if x == var then
        make var stackH xs offset --pominięcie zmiennej, która jest przysłonięta przez argument lambdy
      else
        case entry of
          Stack v -> let (envList, code) = make var stackH xs (offset + 1) in 
            ((x, Heap offset) : envList, [MGetLocal (stackH - v), MSet offset] ++ code) --kopiowanie ze stosu
          Heap v -> let (envList, code) = make var stackH xs (offset + 1) in 
            ((x, Heap offset) : envList, [MGetLocal stackH, MGet v, MSet offset] ++ code) --kopiowanie z innego domknięcia
        
--kompilacja wszystkich globalncyh funkcji
compFunctions :: FuncTable p -> [FunctionDef p] -> [MInstr] -> CompState [MInstr]
compFunctions _ [] code = return code
compFunctions funs (f : fs) code = do
  code1 <- comp funs (envInsert (funcArg f)(Stack 1)(makeInitialEnv [])) 1 (funcBody f) [] 
  compFunctions funs fs (code ++ [MLabel $ getFunctionLabel funs (funcName f)] ++ code1 ++ [MRet])

compile :: [FunctionDef p] -> [Var] -> Expr p -> [MInstr]
compile f v e = 
  let ftable = (makeFuncTable f) in 
  let (code, state) = run (comp (ftable) (makeInitialEnv v) (length v - 1) e []) (length f) in 
  let procedures = fst $ run (compFunctions ftable f []) state in 
  code ++ [MRet] ++ procedures 
  
