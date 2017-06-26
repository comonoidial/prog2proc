{-# LANGUAGE LambdaCase #-}
module Prog2Proc.ProcGen where

import Language.Haskell.Exts
import System.FilePath (pathSeparator)

import Data.Maybe
import Data.Either
import Data.List

test = do 
   ParseOk pm <- parseFile ("." ++ pathSeparator : "Tests" ++ pathSeparator : "QR4.hs")
   let Module _ (Just (ModuleHead _ (ModuleName _ m) _ _)) ps is ds = fmap (const ()) pm
   let mh'= Just (ModuleHead () (ModuleName () (m++"_Proc")) Nothing Nothing)
   let ds' = map (fmap (withUsedLocals . map withVarDefs)) $ lefts $ map getFunDec ds
   let fs = map fst ds'
   let os = filter (\x -> case x of {TypeSig _ [Ident _ f] _ -> f `notElem` fs; _ -> True}) $ rights (map getFunDec ds) 
   mapM_ (\(f,cs) -> (putStrLn f >> mapM_ (putStrLn . show) cs)) ds'
   let xs = genCode $ concatMap snd ds'
   putStrLn $ prettyPrint $ (Module () mh' ps is (os ++ xs))

test2 = do 
   ParseOk m <- parseFile ("." ++ pathSeparator : "Tests" ++ pathSeparator : "BinGCD.hs")
   let Module _ _ _ _ ds = fmap (const ()) m
   mapM_ (putStrLn . show) ds

getFunDec (PatBind _ (PVar _ (Ident _ f)) (UnGuardedRhs _ (Do _ xs)) _) = Left (f, splitSeq (Args f []) xs)
getFunDec (FunBind _ [Match _ (Ident _ f) vs (UnGuardedRhs _ (Do _ xs)) _]) = Left (f, splitSeq (Args f $ map getArg vs) xs)
getFunDec d = Right d

getArg (PVar _ (Ident _ x)) = x

data Cycle a l = Cycle a Source [Action l] (Target l) deriving Show

data Source
   = Args String [String]
   | Results [String]
   | Step
   | LoopExit
   | LoopBegin String
   deriving Show

data Target l
   = Call String [Exp l]
   | Jump String [Exp l] -- tail call
   | Return [Exp l]
   | Next
   | LoopEnter Integer   -- with counter start value
   | LoopEnd Integer    -- with counter max value
   deriving Show

data Action l
   = Logic String (Exp l)
   | Receive String
   | Emit (Exp l)
   | Alloc String (Exp l)
   | Load String String
   | Store String (Exp l)
   | Start String String [Exp l]
   | Finish String String
   deriving Show

splitSeq :: Show l => Source -> [Stmt l] -> [Cycle () l]
splitSeq s = splitS [] where
   splitS xs [] = [Cycle () s (reverse xs) (Return [])]
   splitS xs (Qualifier _ (Var _ (UnQual _ (Ident _ "clock"))) : ys) = Cycle () s (reverse xs) Next : splitSeq Step ys
   splitS xs (Qualifier _ (InfixApp _ (Var _ (UnQual _ (Ident _ r))) (QVarOp _ (UnQual _ (Symbol _ "<~"))) e) : ys) = splitS (Store r e : xs) ys
   splitS xs (Qualifier q (InfixApp _ (App _ (App _ (Var v (UnQual u (Ident l "loop"))) (Lit _ (Int _ n _))) lm) (QVarOp _ (UnQual _ (Symbol _ "$"))) (Lambda _ [PVar _ (Ident _ i)] (Do _ bs))) : ys)
      = Cycle () s (reverse xs) (LoopEnter n) : splitSeq (LoopBegin i) (bs ++ loopEnd) ++ splitSeq LoopExit ys
         where loopEnd = [Qualifier q (App v (Var v (UnQual u (Ident l "LoopEnd"))) lm)]
   splitS xs (Generator _ r (InfixApp _ (Var _ (UnQual _ (Ident _ "call"))) (QVarOp _ (UnQual _ (Symbol _ "$"))) c) : ys)
      | (Var _ (UnQual _ (Ident _ f)) : as) <- flattenApps c = Cycle () s (reverse xs) (Call f as) : splitSeq (Results [getArg r]) ys
   splitS xs (Generator _ r (Var _ (UnQual _ (Ident _ "receive"))) : ys) = splitS (Receive (getArg r) : xs) ys
   splitS xs (Generator _ r (App _ (Var _ (UnQual _ (Ident _ "alloc"))) i) : ys) = splitS (Alloc (getArg r) i : xs) ys
   splitS xs (Generator _ x (App _ (Var _ (UnQual _ (Ident _ "use"))) (Var _ (UnQual _ (Ident _ r)))) : ys) = splitS (Load (getArg x) r : xs) ys
   splitS xs (LetStmt _ (BDecls _ [PatBind _ r (UnGuardedRhs _ e) _]) : ys) = splitS (Logic (getArg r) e : xs) ys
   splitS xs (Qualifier _ (App _ (Var _ (UnQual _ (Ident _ "emit"))) e) : ys) = splitS (Emit e : xs) ys
   splitS xs [Qualifier _ (App _ (Var _ (UnQual _ (Ident _ "return"))) e)] = [Cycle () s (reverse xs) (Return [e])]
   splitS xs [Qualifier _ (App _ (Var _ (UnQual _ (Ident _ "LoopEnd"))) (Lit _ (Int _ m _)))] = [Cycle () s (reverse xs) (LoopEnd m)]
   splitS xs [Qualifier _ (InfixApp _ (Var _ (UnQual _ (Ident _ "call"))) (QVarOp _ (UnQual _ (Symbol _ "$"))) c)] 
      | (Var _ (UnQual _ (Ident _ f)) : as) <- flattenApps c = [Cycle () s (reverse xs) (Jump f as)]
   splitS xs (y : ys) = error (show y) -- splitS xs ys

flattenApps (App _ f x) = flattenApps f ++ [x]
flattenApps (InfixApp _ x (QVarOp l f) y) = [Var l f, x, y]
flattenApps e           = [e]

type VarDefs = [String]

withVarDefs :: Cycle a l -> Cycle VarDefs l
withVarDefs (Cycle _ s xs t) = Cycle (concatMap vdefs xs) s xs t where
   vdefs (Logic x _) = [x]
   vdefs (Receive x) = [x]
   vdefs (Load x _)  = [x]
   vdefs _           = []

sourceVarDefs :: Source -> [String]
sourceVarDefs (Args _   xs) = xs
sourceVarDefs (Results  xs) = xs
sourceVarDefs (LoopBegin i) = [i]
sourceVarDefs _             = []

type UsedLocals = [String]

withUsedLocals :: Show l => [Cycle VarDefs l] -> [Cycle (VarDefs, UsedLocals) l]
withUsedLocals = withULs [] where
   withULs _  [] = []
   withULs vs (Cycle ds s xs t : cs) = Cycle (ds,us) s xs t : withULs vs' cs where
      vs' = sourceVarDefs s ++ ds ++ vs
      us  = nub $ filter (`elem` vs') (concatMap usedVarsA xs ++ usedVarsT t)

data Clause = Clause {cName :: String, cArgs :: [Maybe String], cExp :: Exp (), cWhere :: Maybe (Binds ())}

clauseCon :: Clause -> Exp ()
clauseCon (Clause c _ _ _) = Con () (UnQual () (Ident () c))

componentCode :: String -> [Clause] -> Decl ()
componentCode f = FunBind () . map (\(Clause c xs e mw) ->  Match () (Ident () f) (PApp () (UnQual () (Ident () c)) [] : map pArg xs) (UnGuardedRhs () e) mw) where
   pArg = maybe (PWildCard ()) (PVar () . Ident ())

genAluClause :: Show l => Int -> Cycle (a, UsedLocals) l -> Maybe Clause
genAluClause n (Cycle (_, us) _ xs _) = case [(x, e) | Logic x e <- xs] of
   [] -> Nothing
   as -> Just (Clause ("Op_" ++ show n) (groupArgs $ filter (`elem` us) $ concatMap (usedVarsE . snd) as) (Tuple () Boxed $ map (Var () . UnQual () . Ident ()) $ groupRes $ map fst as) $
      Just (BDecls () $ map (\(x,e) -> PatBind () (PVar () (Ident () x)) (UnGuardedRhs () $ fmap (const ()) e) Nothing) as))

groupArgs :: [String] -> [Maybe String]
groupArgs xs = take 2 (map Just (filter ((< 'p') . head) xs) ++ repeat Nothing) ++ take 2 (map Just (filter ((>= 'p') . head) xs) ++ repeat Nothing)

groupRes xs = take 1 ((filter ((< 'p') . head) xs) ++ repeat "undefined") ++ take 1 ((filter ((>= 'p') . head) xs) ++ repeat "undefined")

aluBody :: String -> [String] -> [(String, Exp l)] -> Maybe (Match ())
aluBody c xs [] = Nothing
aluBody c xs es = Just $ Match () (Ident () "alu") (PApp () (UnQual () (Ident () c)) [] : map (\x -> (PVar () (Ident () x))) xs) (UnGuardedRhs () (Tuple () Boxed $ map (Var () . UnQual () . Ident () . fst) es)) $
   Just (BDecls () $ map (\(x,e) -> PatBind () (PVar () (Ident () x)) (UnGuardedRhs () $ fmap (const ()) e) Nothing) es)

genCode :: Show l => [Cycle (a, UsedLocals) l] -> [Decl ()]
genCode cs = [genDataCon "Label" (map (\(c,_,_)->c) ds), componentCode "microCode" mc, genDataCon "AluOp" ("AluNop" : map cName acs'), componentCode "alu" acs'] where
   acs = zipWith genAluClause [0..] cs
   acs' = catMaybes acs
   ds = genControl 0 [] cs
   mc = zipWith (\(c,xs,e) ac -> Clause c (map Just xs) (Tuple () Boxed [e, ac]) Nothing) ds $ map (maybe (Con () (UnQual () (Ident () "AluNop"))) clauseCon) acs

genControl :: Int -> [String] -> [Cycle a l] -> [(String, [String] , Exp ())]
genControl n ls [] = []
genControl n (l:ls) (Cycle _ s _ (LoopEnd m) : xs) = (labelName n s, [], ce) : genControl (n+1) ls xs where
   ce = App () (App () (Con () (UnQual () (Ident () "LoopBack"))) (Lit () (Int () m (show m)))) (Con () (UnQual () (Ident () l))) 
genControl n ls (Cycle _ s _ t : xs) = (labelName n s, [], controlExp t) : genControl (n+1) ls' xs where 
   ls' = case t of {LoopEnter _ -> ("L_" ++ show (n+1)) : ls; _ -> ls}

labelName n (Args f _ )   = "F_" ++ f
labelName n (LoopBegin _) = "L_" ++ show n
labelName n _             = "C_" ++ show n

controlExp Next          = Con () (UnQual () (Ident () "NextPC"))
controlExp (Return _)    = Con () (UnQual () (Ident () "Return"))
controlExp (Call f _)    = App () (Con () (UnQual () (Ident () "Call"))) (Con () (UnQual () (Ident () ("F_" ++ f))))
controlExp (Jump f _)    = App () (Con () (UnQual () (Ident () "Jump"))) (Con () (UnQual () (Ident () ("F_" ++ f))))
controlExp (LoopEnter i) = App () (Con () (UnQual () (Ident () "LoopInit"))) (Lit () (Int () i (show i)))
controlExp (LoopEnd _)   = error "controlExp LoopEnd"

genDataCon :: String -> [String] -> Decl ()
genDataCon d xs = DataDecl () (DataType ()) Nothing (DHead () (Ident () d)) 
   (map (\x -> QualConDecl () Nothing Nothing (ConDecl () (Ident () x) [])) xs)
   (Just (Deriving () [IRule () Nothing Nothing (IHCon () (UnQual () (Ident () "Enum"))),IRule () Nothing Nothing (IHCon () (UnQual () (Ident () "Show")))]))

usedVarsA :: Show l => Action l -> [String]
usedVarsA (Logic _ e) = usedVarsE e
usedVarsA (Emit    e) = usedVarsE e
usedVarsA (Store _ e) = usedVarsE e
usedVarsA (Alloc _ e) = usedVarsE e
usedVarsA _           = []

usedVarsT :: Show l => Target l -> [String]
usedVarsT (Call _ xs) = concatMap usedVarsE xs
usedVarsT (Jump _ xs) = concatMap usedVarsE xs
usedVarsT (Return xs) = concatMap usedVarsE xs
usedVarsT _           = []

usedVarsE :: Show l => Exp l -> [String]
usedVarsE (Var _ n) = usedVarsN n
usedVarsE (Con _ _) = []
usedVarsE (Lit _ _) = []
usedVarsE (InfixApp _ x _ y) = usedVarsE x ++ usedVarsE y
usedVarsE (App _ f x) = usedVarsE f ++ usedVarsE x
usedVarsE (NegApp _ e) = usedVarsE e
usedVarsE (If _ c t e) = usedVarsE c ++ usedVarsE t ++ usedVarsE e
usedVarsE (Tuple _ _ xs) = concatMap usedVarsE xs
usedVarsE (List _ xs) = concatMap usedVarsE xs
usedVarsE (Paren _ e) = usedVarsE e
usedVarsE (ExpTypeSig _ e _) = usedVarsE e
usedVarsE e = error ("unsupported expression: " ++ show e)

usedVarsN :: QName l -> [String]
usedVarsN (UnQual _ (Ident _ x)) = [x]
usedVarsN _                      = []
