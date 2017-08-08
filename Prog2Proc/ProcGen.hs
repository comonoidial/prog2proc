{-# LANGUAGE LambdaCase #-}
module Prog2Proc.ProcGen where

import Language.Haskell.Exts
import System.FilePath (pathSeparator)

import Data.Maybe
import Data.Either
import Data.List

test fn = do 
   ParseOk pm <- parseFile ("." ++ pathSeparator : "Tests" ++ pathSeparator : fn ++ ".hs")
   let Module _ (Just (ModuleHead _ (ModuleName _ m) _ _)) ps is ds = fmap (const ()) pm
   let mh'= Just (ModuleHead () (ModuleName () (m++"_Proc")) Nothing Nothing)
   let ds' = map (fmap (withStoredVars . withUsedLocals . map withVarDefs)) $ lefts $ map getFunDec ds
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
getFunDec (FunBind _ [Match _ (Ident _ f) vs (UnGuardedRhs _ (Do _ xs)) _]) = Left (f, splitSeq (Args f $ concatMap getBinders vs) xs)
getFunDec d = Right d

getBinder (PVar _ (Ident _ x)) = x
getBinder x = error ("getBinder " ++ show x)

getBinders (PVar _ (Ident _ x)) = [x]
getBinders (PTuple _ Boxed xs) = concatMap getBinders xs
getBinders (PList _ xs) = concatMap getBinders xs
getBinders x = error ("getBinders " ++ show x)

getRef (Var _ (UnQual _ (Ident _ r))) = MemRef r
getRef (InfixApp _ (Var _ (UnQual _ (Ident _ r))) (QVarOp _ (UnQual _ (Symbol _ "?"))) i) = IxRef r i
getRef (Paren _ r) = getRef r
getRef x = error ("getRef " ++ show x)

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
   | Inline String [Exp l]
   | Return [Exp l]
   | Next
   | LoopEnter Integer   -- with counter start value
   | LoopEnd (Exp l)    -- with counter max value
   deriving Show

data Action l
   = Logic [String] (Exp l)
   | Receive [String]
   | Emit (Exp l)
   | Alloc String (Exp l)
   | AllocArr String Integer
   | Load String (Ref l)
   | Store (Ref l) (Exp l)
   | Start String String [Exp l]
   | Finish [String] String
   | Inject String (Exp l)
   | Extract [String] String
   deriving Show

data Ref l = MemRef String | IxRef String (Exp l) deriving Show

splitSeq :: Show l => Source -> [Stmt l] -> [Cycle () l]
splitSeq s = splitS [] where
   splitS xs [] = [Cycle () s (reverse xs) (Return [])]
   splitS xs (Qualifier _ (Var _ (UnQual _ (Ident _ "clock"))) : ys) = Cycle () s (reverse xs) Next : splitSeq Step ys
   splitS xs (Qualifier _ (InfixApp _ r (QVarOp _ (UnQual _ (Symbol _ "<~"))) e) : ys) = splitS (Store (getRef r) e : xs) ys
   splitS xs (Qualifier _ (InfixApp _ (InfixApp w r (QVarOp _ (UnQual _ (Symbol _  "<~"))) a) op b) : ys) = splitS (Store (getRef r) (InfixApp w a op b) : xs) ys
   splitS xs (Qualifier q (InfixApp _ (App _ (App _ (App _ (Var v (UnQual u (Ident l "loop"))) (Lit _ (Int _ n _))) (Var _ (UnQual _ (Ident _ dir)))) lm) (QVarOp _ (UnQual _ (Symbol _ "$"))) (Lambda _ [PVar _ (Ident _ i)] (Do _ bs))) : ys)
      = Cycle () s (reverse xs) (LoopEnter n) : splitSeq (LoopBegin i) (bs ++ loopEnd) ++ splitSeq LoopExit ys
         where loopEnd = [Qualifier q (App v (Var v (UnQual u (Ident l "LoopEnd"))) lm)]
   splitS xs (Qualifier _ (InfixApp _ (Var _ (UnQual _ (Ident _ "call"))) (QVarOp _ (UnQual _ (Symbol _ "$"))) c) : ys) 
      | (Var _ (UnQual _ (Ident _ f)) : as) <- flattenApps c = Cycle () s (reverse xs) (Call f $ concatMap flattenArg as) : splitSeq (Results []) ys
   splitS xs (Qualifier _ (InfixApp _ (Var _ (UnQual _ (Ident _ "inline"))) (QVarOp _ (UnQual _ (Symbol _ "$"))) c) : ys) 
      | (Var _ (UnQual _ (Ident _ f)) : as) <- flattenApps c = Cycle () s (reverse xs) (Inline f $ concatMap flattenArg as) : splitSeq (Results []) ys
   splitS xs (Qualifier _ (App _ (App _ (Var _ (UnQual _ (Ident _ "inject"))) (Var _ (UnQual _ (Ident _ c)))) e) : ys) = splitS (Inject c e : xs) ys
   splitS xs (Qualifier _ (App _ (Var _ (UnQual _ (Ident _ "finish"))) (Var _ (UnQual _ (Ident _ c)))) : ys) = splitS (Finish [] c : xs) ys
   splitS xs (Generator _ r (InfixApp _ (Var _ (UnQual _ (Ident _ "call"))) (QVarOp _ (UnQual _ (Symbol _ "$"))) c) : ys)
      | (Var _ (UnQual _ (Ident _ f)) : as) <- flattenApps c = Cycle () s (reverse xs) (Call f $ concatMap flattenArg as) : splitSeq (Results (getBinders r)) ys
   splitS xs (Generator _ r (InfixApp _ (Var _ (UnQual _ (Ident _ "inline"))) (QVarOp _ (UnQual _ (Symbol _ "$"))) c) : ys)
      | (Var _ (UnQual _ (Ident _ f)) : as) <- flattenApps c = Cycle () s (reverse xs) (Inline f $ concatMap flattenArg as) : splitSeq (Results (getBinders r)) ys
   splitS xs (Generator _ r (Var _ (UnQual _ (Ident _ "receive"))) : ys) = splitS (Receive (getBinders r) : xs) ys
   splitS xs (Generator _ r (App _ (Var _ (UnQual _ (Ident _ "alloc"))) i) : ys) = splitS (Alloc (getBinder r) i : xs) ys
   splitS xs (Generator _ r (App _ (Var _ (UnQual _ (Ident _ "allocArr"))) (Lit _ (Int _ n _))) : ys) = splitS (AllocArr (getBinder r) n : xs) ys
   splitS xs (Generator _ x (App _ (Var _ (UnQual _ (Ident _ "peek"))) r) : ys) = splitS (Load (getBinder x) (getRef r) : xs) ys
   splitS xs (Generator _ x (App _ (Var _ (UnQual _ (Ident _ "finish"))) (Var _ (UnQual _ (Ident _ r)))) : ys) = splitS (Finish (getBinders x) r : xs) ys
   splitS xs (Generator _ x (App _ (Var _ (UnQual _ (Ident _ "start"))) (Var _ (UnQual _ (Ident _ c)))) : ys) = splitS (Start (getBinder x) c [] : xs) ys
   splitS xs (Generator _ x (InfixApp _ (Var _ (UnQual _ (Ident _ "start"))) (QVarOp _ (UnQual _ (Symbol _ "$"))) s) : ys) 
      | (Var _ (UnQual _ (Ident _ c)) : as) <- flattenApps s = splitS (Start (getBinder x) c (concatMap flattenArg as) : xs) ys
   splitS xs (Generator _ x (App _ (Var _ (UnQual _ (Ident _ "extract"))) (Var _ (UnQual _ (Ident _ c)))) : ys) = splitS (Extract (getBinders x) c : xs) ys
   splitS xs (LetStmt _ (BDecls _ [PatBind _ r (UnGuardedRhs _ e) _]) : ys) = splitS (Logic (getBinders r) e : xs) ys
   splitS xs (Qualifier _ (App _ (Var _ (UnQual _ (Ident _ "emit"))) e) : ys) = splitS (Emit e : xs) ys
   splitS xs [Qualifier _ (App _ (Var _ (UnQual _ (Ident _ "return"))) e)] = [Cycle () s (reverse xs) (Return $ flattenArg e)]
   splitS xs [Qualifier _ (App _ (Var _ (UnQual _ (Ident _ "LoopEnd"))) m)] = [Cycle () s (reverse xs) (LoopEnd m)]
   splitS xs [Qualifier _ (InfixApp _ (Var _ (UnQual _ (Ident _ "call"))) (QVarOp _ (UnQual _ (Symbol _ "$"))) c)] 
      | (Var _ (UnQual _ (Ident _ f)) : as) <- flattenApps c = [Cycle () s (reverse xs) (Jump f $ concatMap flattenArg as)]
   splitS xs [Qualifier _ (InfixApp _ (Var _ (UnQual _ (Ident _ "inline"))) (QVarOp _ (UnQual _ (Symbol _ "$"))) c)] 
      | (Var _ (UnQual _ (Ident _ f)) : as) <- flattenApps c = [Cycle () s (reverse xs) (Inline f $ concatMap flattenArg as)]
   splitS xs (y : ys) = error (show y) -- splitS xs ys

flattenApps (App _ f x) = flattenApps f ++ [x]
flattenApps (InfixApp _ x (QVarOp l f) y) = [Var l f, x, y]
flattenApps e           = [e]

flattenArg (List _ xs) = xs
flattenArg (Tuple _ Boxed xs) = concatMap flattenArg xs
flattenArg x = [x]

type VarDefs = [String]

withVarDefs :: Cycle a l -> Cycle VarDefs l
withVarDefs (Cycle _ s xs t) = Cycle (concatMap vdefs xs) s xs t where
   vdefs (Logic xs _)  = xs
   vdefs (Receive xs)  = xs
   vdefs (Load x _ )   = [x]
   vdefs (Finish xs _) = xs
   vdefs _             = []

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

type StoredDefs = [String]

withStoredVars :: [Cycle (VarDefs, UsedLocals) l] -> [Cycle (StoredDefs, UsedLocals) l]
withStoredVars = id -- TODO only keep vars live across cycle boundaries

data Clause = Clause {cName :: String, cArgs :: [Maybe String], cExp :: Exp (), cWhere :: Maybe (Binds ())}

clauseCon :: Clause -> Exp ()
clauseCon (Clause c _ _ _) = Con () (UnQual () (Ident () c))

componentCode :: String -> [Clause] -> Decl ()
componentCode f = FunBind () . map (\(Clause c xs e mw) ->  Match () (Ident () f) (PApp () (UnQual () (Ident () c)) [] : map pArg xs) (UnGuardedRhs () e) mw) where
   pArg = maybe (PWildCard ()) (PVar () . Ident ())

genAluClause :: Show l => Int -> Cycle (a, UsedLocals) l -> Maybe Clause
genAluClause n (Cycle (_, us) _ as _) = case [(xs, e) | Logic xs e <- as] of
   [] -> Nothing
   es -> Just (Clause ("Op_" ++ show n) (groupArgs $ filter (`elem` us) $ concatMap (usedVarsE . snd) es) (Tuple () Boxed $ map (Var () . UnQual () . Ident ()) $ groupRes $ concatMap fst es) $
      Just (BDecls () $ map (\(xs,e) -> PatBind () (genBinders xs) (UnGuardedRhs () $ fmap (const ()) e) Nothing) es))

genBinders [x] = (PVar () (Ident () x))
genBinders xs  = PTuple () Boxed (map (PVar () . Ident ()) xs)

groupArgs :: [String] -> [Maybe String]
groupArgs xs = take 2 (map Just (filter ((< 'p') . head) xs) ++ repeat Nothing) ++ take 2 (map Just (filter ((>= 'p') . head) xs) ++ repeat Nothing)

groupRes xs = take 1 ((filter ((< 'p') . head) xs) ++ repeat "undefined") ++ take 1 ((filter ((>= 'p') . head) xs) ++ repeat "undefined")

genCode :: [Cycle (StoredDefs, UsedLocals) ()] -> [Decl ()]
genCode cs = [ctrlData, genDataCon "Label" (map (\(c,_,_)->c) ds), control, componentCode "microCode" mc, genDataCon "AluOp" ("AluNop" : map cName acs'), componentCode "alu" acs'] where
   acs = zipWith genAluClause [0..] cs
   acs' = catMaybes acs
   ds = genControl 0 [] cs
   mls = genMemOps ([],[]) cs
   mc = zipWith3 (\(c,xs,e) ac ls -> Clause c (map Just xs) (Tuple () Boxed ([e, ac] ++ ls)) Nothing) ds (map (maybe (Con () (UnQual () (Ident () "AluNop"))) clauseCon) acs) mls

genControl :: Int -> [String] -> [Cycle a ()] -> [(String, [String] , Exp ())]
genControl n ls [] = []
genControl n (l:ls) (Cycle _ s _ (LoopEnd m) : xs) = (labelName n s, [], ce) : genControl (n+1) ls xs where
   ce = App () (App () (Con () (UnQual () (Ident () "LoopBack"))) m) (Con () (UnQual () (Ident () l))) 
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

genMemOps :: ([String],[String]) -> [Cycle (StoredDefs, UsedLocals) l] -> [[Exp ()]]
genMemOps (v1s, v2s) [] = []
genMemOps (v1s, v2s) (Cycle (ns, ls) s _ _ : cs) = (lcs ++ [genStore v1s' n1s, genStore v2s' n2s]) : genMemOps (n1s++v1s', n2s++v2s') cs where
   (n1s, n2s) = partition ((< 'p') . head) ns
   (v1s', v2s') = loadableVars (v1s, v2s) s
   (l1s, l2s) = partition ((< 'p') . head) ls
   lcs = take 2 (map (genLoad v1s') (l1s ++ repeat "")) ++ take 2 (map (genLoad v2s') (l2s ++ repeat ""))
   genLoad vs x = Lit () (Int () i (show i)) where i = maybe 0 fromIntegral $ elemIndex x vs
   genStore vs []    = Con () (UnQual () (Ident () "Nothing"))
   genStore vs (x:_) = App () (Con () (UnQual () (Ident () "Just"))) (Lit () (Int () i (show i))) 
                        where i = fromIntegral $ length vs

loadableVars :: ([String],[String]) -> Source -> ([String],[String])
loadableVars (v1s, v2s) (Args _  xs) = partition ((< 'p') . head) xs
loadableVars (v1s, v2s) (Results rs) = let (xs, ys) = partition ((< 'p') . head) rs in (xs ++ v1s, ys ++ v2s)
loadableVars (v1s, v2s) _            = (v1s, v2s)

ctrlData :: Decl ()
ctrlData = DataDecl () (DataType ()) Nothing (DHead () (Ident () "Ctrl")) 
   [QualConDecl () Nothing Nothing (ConDecl () (Ident () "NextPC") [])
   ,QualConDecl () Nothing Nothing (ConDecl () (Ident () "Return") [])
   ,QualConDecl () Nothing Nothing (ConDecl () (Ident () "Branch") [TyCon () (UnQual () (Ident () "Label"))])
   ,QualConDecl () Nothing Nothing (ConDecl () (Ident () "Call") [TyCon () (UnQual () (Ident () "Label"))])
   ,QualConDecl () Nothing Nothing (ConDecl () (Ident () "Jump") [TyCon () (UnQual () (Ident () "Label"))])
   ] Nothing

control :: Decl ()
control = FunBind () 
   [Match () (Ident () "ctrl") 
     [PApp () (UnQual ()(Ident () "NextPC")) [],PWildCard (),PVar () (Ident () "nPC"),PVar () (Ident () "cSP"),PVar () (Ident () "retPC")]
     (UnGuardedRhs () (Tuple () Boxed [Var () (UnQual () (Ident () "cSP")),Con () (UnQual () (Ident () "Nothing")),Var () (UnQual () (Ident () "nPC"))])) Nothing
   ,Match () (Ident () "ctrl") 
      [PApp () (UnQual () (Ident () "Return")) [],PWildCard (),PVar () (Ident () "nPC"),PVar () (Ident () "cSP"),PVar () (Ident () "retPC")]
      (UnGuardedRhs () (Tuple () Boxed [InfixApp () (Var () (UnQual () (Ident () "cSP"))) (QVarOp () (UnQual () (Symbol () "-"))) (Lit () (Int () 1 "1")),Con () (UnQual () (Ident () "Nothing")),Var () (UnQual () (Ident () "retPC"))])) Nothing
   ,Match () (Ident () "ctrl") 
      [PParen () (PApp () (UnQual () (Ident () "Branch")) [PVar () (Ident () "e")]),PLit () (Signless ()) (Int () 0 "0"),PVar () (Ident () "nPC"),PVar () (Ident () "cSP"),PVar () (Ident () "retPC")]
     (UnGuardedRhs () (Tuple () Boxed [Var () (UnQual () (Ident () "cSP")),Con () (UnQual () (Ident () "Nothing")),Var () (UnQual () (Ident () "e"))])) Nothing
   ,Match () (Ident () "ctrl") 
      [PParen () (PApp () (UnQual () (Ident () "Branch")) [PVar () (Ident () "e")]),PVar () (Ident () "c"),PVar () (Ident () "nPC"),PVar () (Ident () "cSP"),PVar () (Ident () "retPC")]
      (UnGuardedRhs () (Tuple () Boxed [Var () (UnQual () (Ident () "cSP")),Con () (UnQual () (Ident () "Nothing")),Var () (UnQual () (Ident () "nPC"))])) Nothing
   ,Match () (Ident () "ctrl") 
      [PParen () (PApp () (UnQual () (Ident () "Call")) [PVar () (Ident () "f")]),PWildCard (),PVar () (Ident () "nPC"),PVar () (Ident () "cSP"),PVar () (Ident () "retPC")] 
      (UnGuardedRhs () (Tuple () Boxed [InfixApp () (Var () (UnQual () (Ident () "cSP"))) (QVarOp () (UnQual () (Symbol () "+"))) (Lit () (Int () 1 "1")),App () (Con () (UnQual ()(Ident () "Just"))) (Tuple () Boxed [InfixApp () (Var () (UnQual () (Ident () "cSP"))) (QVarOp () (UnQual () (Symbol() "+"))) (Lit () (Int () 1 "1")),Var () (UnQual () (Ident () "nPC"))]),Var () (UnQual () (Ident () "f"))])) Nothing
   ,Match () (Ident () "ctrl") 
      [PParen () (PApp () (UnQual () (Ident () "Jump")) [PVar () (Ident () "f")]),PWildCard (),PVar () (Ident () "nPC"),PVar () (Ident () "cSP"),PVar () (Ident () "retPC")] 
     (UnGuardedRhs () (Tuple () Boxed [Var () (UnQual () (Ident () "cSP")),Con () (UnQual () (Ident () "Nothing")),Var () (UnQual () (Ident () "f"))])) Nothing
   ]


usedVarsA :: Show l => Action l -> [String]
usedVarsA (Logic _ e) = usedVarsE e
usedVarsA (Emit    e) = usedVarsE e
usedVarsA (Store _ e) = usedVarsE e
usedVarsA (Alloc _ e) = usedVarsE e
usedVarsA (Start _ _ xs) = concatMap usedVarsE xs
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
