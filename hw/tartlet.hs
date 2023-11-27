{-# OPTIONS_GHC -W #-}

module Main where
import Data.Foldable (for_)

-- This file is a type checker for a smaller relative of Pie, called Tartlet.
--
-- Tartlet is like Pie, with the following exceptions:
--
--  1. There is no syntactic sugar such as -> and Pair types, or
--     functions with multiple arguments.
--
--  2. The type U describes _all_ types, including itself. Thus, there
--     is no need for the forms of judgment:
--       * ____ is a type
--       * ____ and ____ are the same type
--
--  3. Some type constructors in Pie are missing, such as Either.

-- Your tasks:
--
-- 1. Add the type Either. Use the following grammar and rules:
--
--  e ::= ...
--      | (Either e e)
--
--  Γ ⊢ A ⇐ U   Γ ⊢ B ⇐ U
-- ------------------------
--   Γ ⊢ (Either A B) ⇒ U
--
-- Remember to update alphaEquiv and readBackTyped.
--
-- 2. Add the introduction forms for Either. Use the following grammar and rules:
--
--  e ::= ...
--      | (left e)
--      | (right e)
--
--          Γ ⊢ e ⇐ A
-- -----------------------------
--  Γ ⊢ (left e) ⇐ (Either A B)
--
--           Γ ⊢ e ⇐ B
-- -----------------------------
--  Γ ⊢ (right e) ⇐ (Either A B)
--
-- You'll need to pick names other than "Left" and "Right", because
-- these are already taken for Haskell's own Either type. I suggest
-- "Lft" and "Rght".
--
-- Each is worth 1 point (2 total for this question)
--
-- 3. Add the elimination rule for Either. Use the following grammar and rules:
--
--   e ::= ...
--       | (ind-Either e e e e)
--
--    Γ ⊢ tgt ⇒ (Either A B)
--    Γ ⊢ mot ⇐ (Π ((e (Either A B))) U)
--    Γ ⊢ ell ⇐ (Π ((a A)) (mot (left a)))
--    Γ ⊢ are ⇐ (Π ((b B)) (mot (right b)))
--  ----------------------------------------------
--   Γ ⊢ (ind-Either tgt mot ell are) ⇒ (mot tgt)
--
-- 4. Translate the definitions of evenness and oddness from the book
--    to Tartlet. Add them to evenOddProgram, after the definition of
--    double.
--
-- 5. Prove that zero is even in Tartlet. Add this and the remaining
--    definitions to evenOddProgram as well.
--
-- 6. Prove that adding one to an even number is odd.
--
-- 7. Prove that adding one to an odd number is even.
--
-- 8. Prove that every natural number is either even or odd.
--
-- Hint: To check whether your definitions work, you can load
-- this file in ghci, and evaluate
--   > testFile evenOddProgram
--
-- If the result is Left around a message, type checking failed. If
-- the result is Right around a list of output, then type checking
-- succeeded.
--
-- Remember: there's no "claim" in Tartlet. Definitions and examples
-- need to be expressions for which a type can be synthesized. Use The
-- to make a checkable expression synthesizable.

newtype Name = Name String
    deriving (Show, Eq)

newtype Message = Message String
    deriving (Show)

failure :: String -> Either Message a
failure msg = Left (Message msg)

freshen :: [Name] -> Name -> Name
freshen used x
    | x `elem` used = freshen used (nextName x)
    | otherwise = x

nextName :: Name -> Name
nextName (Name x) = Name (x ++ "'")

data Expr
    = Var Name
    | Pi Name Expr Expr
    | Lambda Name Expr
    | App Expr Expr
    | Sigma Name Expr Expr
    | Cons Expr Expr
    | Car Expr
    | Cdr Expr
    | Nat
    | Zero
    | Add1 Expr
    | IndNat Expr Expr Expr Expr
    | Equal Expr Expr Expr
    | Same
    | Replace Expr Expr Expr
    | Trivial
    | Sole
    | Absurd
    | IndAbsurd Expr Expr
    | Atom
    | Tick String
    | U
    | The Expr Expr
    | Either Expr Expr
    | Lft Expr
    | Rght Expr
    | IndEither Expr Expr Expr Expr
    deriving (Eq, Show)

alphaEquiv :: Expr -> Expr -> Bool
alphaEquiv e1 e2 = alphaEquivHelper 0 [] e1 [] e2

alphaEquivHelper :: Integer -> [(Name, Integer)] -> Expr -> [(Name, Integer)] -> Expr -> Bool
alphaEquivHelper _ ns1 (Var x) ns2 (Var y) =
    case (lookup x ns1, lookup y ns2) of
        (Nothing, Nothing) -> x == y
        (Just i, Just j) -> i == j
        _ -> False
alphaEquivHelper i ns1 (Pi x a1 r1) ns2 (Pi y a2 r2) =
    alphaEquivHelper i ns1 a1 ns2 a2
        && alphaEquivHelper (i + 1) ((x, i) : ns1) r1 ((y, i) : ns2) r2
alphaEquivHelper i ns1 (Lambda x body1) ns2 (Lambda y body2) =
    alphaEquivHelper (i + 1) ((x, i) : ns1) body1 ((y, i) : ns2) body2
alphaEquivHelper i ns1 (App rator1 rand1) ns2 (App rator2 rand2) =
    alphaEquivHelper i ns1 rator1 ns2 rator2
        && alphaEquivHelper i ns1 rand1 ns2 rand2
alphaEquivHelper i ns1 (Sigma x a1 d1) ns2 (Sigma y a2 d2) =
    alphaEquivHelper i ns1 a1 ns2 a2
        && alphaEquivHelper (i + 1) ((x, i) : ns1) d1 ((y, i) : ns2) d2
alphaEquivHelper i ns1 (Cons car1 cdr1) ns2 (Cons car2 cdr2) =
    alphaEquivHelper i ns1 car1 ns2 car2
        && alphaEquivHelper i ns1 cdr1 ns2 cdr2
alphaEquivHelper i ns1 (Car pair1) ns2 (Car pair2) =
    alphaEquivHelper i ns1 pair1 ns2 pair2
alphaEquivHelper i ns1 (Cdr pair1) ns2 (Cdr pair2) =
    alphaEquivHelper i ns1 pair1 ns2 pair2
alphaEquivHelper _ _ Nat _ Nat = True
alphaEquivHelper _ _ Zero _ Zero = True
alphaEquivHelper i ns1 (Add1 e1) ns2 (Add1 e2) =
    alphaEquivHelper i ns1 e1 ns2 e2
alphaEquivHelper i ns1 (IndNat tgt1 mot1 base1 step1) ns2 (IndNat tgt2 mot2 base2 step2) =
    alphaEquivHelper i ns1 tgt1 ns2 tgt2
        && alphaEquivHelper i ns1 mot1 ns2 mot2
        && alphaEquivHelper i ns1 base1 ns2 base2
        && alphaEquivHelper i ns1 step1 ns2 step2
alphaEquivHelper i ns1 (Equal ty1 from1 to1) ns2 (Equal ty2 from2 to2) =
    alphaEquivHelper i ns1 ty1 ns2 ty2
        && alphaEquivHelper i ns1 from1 ns2 from2
        && alphaEquivHelper i ns1 to1 ns2 to2
alphaEquivHelper _ _ Same _ Same = True
alphaEquivHelper i ns1 (Replace tgt1 mot1 base1) ns2 (Replace tgt2 mot2 base2) =
    alphaEquivHelper i ns1 tgt1 ns2 tgt2
        && alphaEquivHelper i ns1 mot1 ns2 mot2
        && alphaEquivHelper i ns1 base1 ns2 base2
alphaEquivHelper _ _ Trivial _ Trivial = True
alphaEquivHelper _ _ Sole _ Sole = True
alphaEquivHelper _ _ Absurd _ Absurd = True
alphaEquivHelper i ns1 (IndAbsurd tgt1 mot1) ns2 (IndAbsurd tgt2 mot2) =
    alphaEquivHelper i ns1 tgt1 ns2 tgt2
        && alphaEquivHelper i ns1 mot1 ns2 mot2
alphaEquivHelper _ _ Atom _ Atom = True
alphaEquivHelper _ _ U _ U = True
alphaEquivHelper _ _ (Tick a1) _ (Tick a2) = a1 == a2
alphaEquivHelper _ _ (The Absurd _) _ (The Absurd _) = True
alphaEquivHelper i ns1 (The t1 e1) ns2 (The t2 e2) =
    alphaEquivHelper i ns1 t1 ns2 t2 && alphaEquivHelper i ns1 e1 ns2 e2
alphaEquivHelper i ns1 (Either t11 t12) ns2 (Either t21 t22) =
    alphaEquivHelper i ns1 t11 ns2 t21 && alphaEquivHelper i ns1 t12 ns2 t22
alphaEquivHelper i ns1 (Lft e1) ns2 (Lft e2) = alphaEquivHelper i ns1 e1 ns2 e2
alphaEquivHelper i ns1 (Rght e1) ns2 (Rght e2) = alphaEquivHelper i ns1 e1 ns2 e2
alphaEquivHelper i ns1 (IndEither tgt1 mot1 ell1 are1) ns2 (IndEither tgt2 mot2 ell2 are2) =
    alphaEquivHelper i ns1 tgt1 ns2 tgt2
        && alphaEquivHelper i ns1 mot1 ns2 mot2
        && alphaEquivHelper i ns1 ell1 ns2 ell2
        && alphaEquivHelper i ns1 are1 ns2 are2
alphaEquivHelper _ _ _ _ _ = False

data Value
    = VPi Ty Closure
    | VLambda Closure
    | VSigma Ty Closure
    | VPair Value Value
    | VNat
    | VZero
    | VAdd1 Value
    | VEq Ty Value Value
    | VSame
    | VTrivial
    | VSole
    | VAbsurd
    | VAtom
    | VTick String
    | VU
    | VNeutral Ty Neutral
    | VEither Ty Ty
    | VLft Value
    | VRght Value
    deriving (Show)

data Closure = Closure
    { closureEnv :: Env
    , closureName :: Name
    , closureBody :: Expr
    }
    deriving (Show)

type Ty = Value

newtype Env = Env [(Name, Value)]
    deriving (Show)

extendEnv :: Env -> Name -> Value -> Env
extendEnv (Env env) x v = Env ((x, v) : env)

evalVar :: Env -> Name -> Value
evalVar (Env []) x = error ("Missing value for " ++ show x)
evalVar (Env ((y, v) : env)) x
    | x == y = v
    | otherwise = evalVar (Env env) x

data Neutral
    = NVar Name
    | NApp Neutral Normal
    | NCar Neutral
    | NCdr Neutral
    | NIndNat Neutral Normal Normal Normal
    | NReplace Neutral Normal Normal
    | NIndAbsurd Neutral Normal
    | NIndEither Neutral Normal Normal Normal
    deriving (Show)

data Normal = Normal Ty Value
    deriving (Show)

data CtxEntry = Def Ty Value | IsA Ty

newtype Ctx = Ctx [(Name, CtxEntry)]

initCtx :: Ctx
initCtx = Ctx []

ctxNames :: Ctx -> [Name]
ctxNames (Ctx ctx) = map fst ctx

extendCtx :: Ctx -> Name -> Ty -> Ctx
extendCtx (Ctx ctx) x t = Ctx ((x, IsA t) : ctx)

define :: Ctx -> Name -> Ty -> Value -> Ctx
define (Ctx ctx) x t v = Ctx ((x, Def t v) : ctx)

lookupType :: Ctx -> Name -> Either Message Ty
lookupType (Ctx []) x =
    failure ("Unbound variable: " ++ show x)
lookupType (Ctx ((y, e) : ctx)) x
    | x == y =
        case e of
            Def t _ -> return t
            IsA t -> return t
    | otherwise =
        lookupType (Ctx ctx) x

mkEnv :: Ctx -> Env
mkEnv (Ctx []) = Env []
mkEnv (Ctx ((x, e) : ctx)) = Env ((x, v) : env)
  where
    Env env = mkEnv (Ctx ctx)
    v = case e of
        Def _ v -> v
        IsA t -> VNeutral t (NVar x)

eval :: Env -> Expr -> Value
eval env (Var x) = evalVar env x
eval env (Pi x dom ran) = VPi (eval env dom) (Closure env x ran)
eval env (Lambda x body) = VLambda (Closure env x body)
eval env (App rator rand) = doApply (eval env rator) (eval env rand)
eval env (Sigma x carType cdrType) =
    VSigma (eval env carType) (Closure env x cdrType)
eval env (Cons a d) = VPair (eval env a) (eval env d)
eval env (Car e) = doCar (eval env e)
eval env (Cdr e) = doCdr (eval env e)
eval _ Nat = VNat
eval _ Zero = VZero
eval env (Add1 e) = VAdd1 (eval env e)
eval env (IndNat tgt mot base step) =
    doIndNat (eval env tgt) (eval env mot) (eval env base) (eval env step)
eval env (Equal ty from to) = VEq (eval env ty) (eval env from) (eval env to)
eval _ Same = VSame
eval env (Replace tgt mot base) =
    doReplace (eval env tgt) (eval env mot) (eval env base)
eval _ Trivial = VTrivial
eval _ Sole = VSole
eval _ Absurd = VAbsurd
eval env (IndAbsurd tgt mot) = doIndAbsurd (eval env tgt) (eval env mot)
eval _ Atom = VAtom
eval _ (Tick x) = VTick x
eval _ U = VU
eval env (The _ e) = eval env e
eval env (Either e1 e2) =
    let tyA = eval env e1
        tyB = eval env e2
     in VEither tyA tyB
eval env (Lft e) = VLft (eval env e)
eval env (Rght e) = VRght (eval env e)
eval env (IndEither tgt mot ell are) = doIndEither (eval env tgt) (eval env mot) (eval env ell) (eval env are)

evalClosure :: Closure -> Value -> Value
evalClosure (Closure env x e) v = eval (extendEnv env x v) e

doCar :: Value -> Value
doCar (VPair v1 _) = v1
doCar (VNeutral (VSigma aT _) neu) =
    VNeutral aT (NCar neu)
doCar _ = error "[Internal Error] not handling pairs"

doCdr :: Value -> Value
doCdr (VPair _ v2) = v2
doCdr v@(VNeutral (VSigma _ dT) neu) =
    VNeutral (evalClosure dT (doCar v)) (NCdr neu)
doCdr _ = error "[Internal Error] not handling pairs"

doApply :: Value -> Value -> Value
doApply (VLambda closure) arg =
    evalClosure closure arg
doApply (VNeutral (VPi dom ran) neu) arg =
    VNeutral (evalClosure ran arg) (NApp neu (Normal dom arg))
doApply _ _ = error "[Internal Error] not handling functions"

doIndAbsurd :: Value -> Value -> Value
doIndAbsurd (VNeutral VAbsurd neu) mot =
    VNeutral mot (NIndAbsurd neu (Normal VU mot))
doIndAbsurd _ _ = error "[Internal Error] not doing induction on absurd values"

doReplace :: Value -> Value -> Value -> Value
doReplace VSame _ base =
    base
doReplace (VNeutral (VEq ty from to) neu) mot base =
    VNeutral
        (doApply mot to)
        (NReplace neu (Normal motT mot) (Normal baseT base))
  where
    motT = VPi ty (Closure (Env []) (Name "x") U)
    baseT = doApply mot from
doReplace _ _ _ = error "[Internal Error] not replacing equality proofs"

indNatStepType :: Value -> Value
indNatStepType mot =
    eval
        (Env [(Name "mot", mot)])
        ( Pi
            (Name "n-1")
            Nat
            ( Pi
                (Name "almost")
                ( App
                    (Var (Name "mot"))
                    (Var (Name "n-1"))
                )
                ( App
                    (Var (Name "mot"))
                    (Add1 (Var (Name "n-1")))
                )
            )
        )

doIndNat :: Value -> Value -> Value -> Value -> Value
doIndNat VZero _ base _ =
    base
doIndNat (VAdd1 v) mot base step =
    doApply (doApply step v) (doIndNat v mot base step)
doIndNat tgt@(VNeutral VNat neu) mot base step =
    VNeutral
        (doApply mot tgt)
        ( NIndNat
            neu
            (Normal (VPi VNat (Closure (Env []) (Name "k") U)) mot)
            (Normal (doApply mot VZero) base)
            (Normal (indNatStepType mot) step)
        )
doIndNat _ _ _ _ = error "[Internal Error] not doing induction on natural numbers"

doIndEither :: Value -> Value -> Value -> Value -> Value
doIndEither (VLft v) _ ell _ = doApply ell v
doIndEither (VRght v) _ _ are = doApply are v
doIndEither _ _ _ _ = error "[Internal Error] not doing induction on value of Either type"

readBackNormal :: Ctx -> Normal -> Expr
readBackNormal ctx (Normal t v) = readBackTyped ctx t v

readBackTyped :: Ctx -> Ty -> Value -> Expr
readBackTyped _ VNat VZero = Zero
readBackTyped ctx VNat (VAdd1 v) = Add1 (readBackTyped ctx VNat v)
readBackTyped ctx (VPi dom ran) fun =
    Lambda
        x
        ( readBackTyped
            (extendCtx ctx x dom)
            (evalClosure ran xVal)
            (doApply fun xVal)
        )
  where
    x = freshen (ctxNames ctx) (closureName ran)
    xVal = VNeutral dom (NVar x)
readBackTyped ctx (VSigma aT dT) pair =
    Cons
        (readBackTyped ctx aT carVal)
        (readBackTyped ctx (evalClosure dT carVal) cdrVal)
  where
    carVal = doCar pair
    cdrVal = doCdr pair
readBackTyped _ VTrivial _ = Sole
readBackTyped ctx VAbsurd (VNeutral VAbsurd neu) =
    The Absurd (readBackNeutral ctx neu)
readBackTyped _ VEq{} VSame = Same
readBackTyped _ VAtom (VTick x) = Tick x
readBackTyped _ VU VNat = Nat
readBackTyped _ VU VAtom = Atom
readBackTyped _ VU VTrivial = Trivial
readBackTyped _ VU VAbsurd = Absurd
readBackTyped ctx VU (VEq t from to) =
    Equal
        (readBackTyped ctx VU t)
        (readBackTyped ctx t from)
        (readBackTyped ctx t to)
readBackTyped ctx VU (VSigma aT dT) = Sigma x a d
  where
    x = freshen (ctxNames ctx) (closureName dT)
    a = readBackTyped ctx VU aT
    d =
        readBackTyped
            (extendCtx ctx x aT)
            VU
            (evalClosure dT (VNeutral aT (NVar x)))
readBackTyped ctx VU (VPi aT bT) = Pi x a b
  where
    x = freshen (ctxNames ctx) (closureName bT)
    a = readBackTyped ctx VU aT
    b =
        readBackTyped
            (extendCtx ctx x aT)
            VU
            (evalClosure bT (VNeutral aT (NVar x)))
readBackTyped _ VU VU = U
readBackTyped ctx _ (VNeutral _ neu) =
    readBackNeutral ctx neu
readBackTyped ctx VU (VEither tyA tyB) =
    Either (readBackTyped ctx VU tyA) (readBackTyped ctx VU tyB)
readBackTyped ctx (VEither tyA _) (VLft a) = Lft (readBackTyped ctx tyA a)
readBackTyped ctx (VEither _ tyB) (VRght b) = Rght (readBackTyped ctx tyB b)
readBackTyped _ otherT otherE = error $ show otherT ++ show otherE

readBackNeutral :: Ctx -> Neutral -> Expr
readBackNeutral _ (NVar x) = Var x
readBackNeutral ctx (NApp neu arg) =
    App (readBackNeutral ctx neu) (readBackNormal ctx arg)
readBackNeutral ctx (NCar neu) = Car (readBackNeutral ctx neu)
readBackNeutral ctx (NCdr neu) = Cdr (readBackNeutral ctx neu)
readBackNeutral ctx (NIndNat neu mot base step) =
    IndNat
        (readBackNeutral ctx neu)
        (readBackNormal ctx mot)
        (readBackNormal ctx base)
        (readBackNormal ctx step)
readBackNeutral ctx (NReplace neu mot base) =
    Replace
        (readBackNeutral ctx neu)
        (readBackNormal ctx mot)
        (readBackNormal ctx base)
readBackNeutral ctx (NIndAbsurd neu mot) =
    IndAbsurd
        (The Absurd (readBackNeutral ctx neu))
        (readBackNormal ctx mot)
readBackNeutral ctx (NIndEither neu mot ell are) =
    IndEither
        (readBackNeutral ctx neu)
        (readBackNormal ctx mot)
        (readBackNormal ctx ell)
        (readBackNormal ctx are)

synth :: Ctx -> Expr -> Either Message Ty
synth ctx (Var x) = lookupType ctx x
synth ctx (Pi x a b) = do
    check ctx a VU
    check (extendCtx ctx x (eval (mkEnv ctx) a)) b VU
    return VU
synth ctx (App rator rand) = do
    funTy <- synth ctx rator
    (a, b) <- isPi ctx funTy
    check ctx rand a
    return (evalClosure b (eval (mkEnv ctx) rand))
synth ctx (Sigma x a b) = do
    check ctx a VU
    check (extendCtx ctx x (eval (mkEnv ctx) a)) b VU
    return VU
synth ctx (Car e) = do
    t <- synth ctx e
    (aT, _) <- isSigma ctx t
    return aT
synth ctx (Cdr e) = do
    t <- synth ctx e
    (_, dT) <- isSigma ctx t
    return (evalClosure dT (doCar (eval (mkEnv ctx) e)))
synth _ Nat = return VU
synth ctx (IndNat tgt mot base step) = do
    t <- synth ctx tgt
    isNat ctx t
    let tgtV = eval (mkEnv ctx) tgt
        motTy = eval (Env []) (Pi (Name "x") Nat U)
    check ctx mot motTy
    let motV = eval (mkEnv ctx) mot
    check ctx base (doApply motV VZero)
    check ctx step (indNatStepType motV)
    return (doApply motV tgtV)
synth ctx (Equal ty from to) = do
    check ctx ty VU
    let tyV = eval (mkEnv ctx) ty
    check ctx from tyV
    check ctx to tyV
    return VU
synth ctx (Replace tgt mot base) = do
    t <- synth ctx tgt
    (ty, from, to) <- isEqual ctx t
    let motTy = eval (Env [(Name "ty", ty)]) (Pi (Name "x") (Var (Name "ty")) U)
    check ctx mot motTy
    let motV = eval (mkEnv ctx) mot
    check ctx base (doApply motV from)
    return (doApply motV to)
synth _ Trivial = return VU
synth _ Absurd = return VU
synth ctx (IndAbsurd tgt mot) = do
    t <- synth ctx tgt
    isAbsurd ctx t
    check ctx mot VU
    return (eval (mkEnv ctx) mot)
synth _ Atom = return VU
synth _ U = return VU
synth ctx (The ty expr) = do
    check ctx ty VU
    let tyV = eval (mkEnv ctx) ty
    check ctx expr tyV
    return tyV
--  Γ ⊢ A ⇐ U   Γ ⊢ B ⇐ U
-- ------------------------
--   Γ ⊢ (Either A B) ⇒ U
synth ctx (Either a b) = do
    check ctx a VU
    check ctx b VU
    return VU
--    Γ ⊢ tgt ⇒ (Either A B)
--    Γ ⊢ mot ⇐ (Π ((e (Either A B))) U)
--    Γ ⊢ ell ⇐ (Π ((a A)) (mot (left a)))
--    Γ ⊢ are ⇐ (Π ((b B)) (mot (right b)))
--  ----------------------------------------------
--   Γ ⊢ (ind-Either tgt mot ell are) ⇒ (mot tgt)
synth ctx (IndEither tgt mot ell are) = do
    tyTgt <- synth ctx tgt
    (tyA, tyB) <- isEither ctx tyTgt
    let motTy = eval (Env [(Name "ty", tyTgt)]) (Pi (Name "e") (Var (Name "ty")) U)
        motV = eval (mkEnv ctx) mot
        ellTy = eval (Env [(Name "mot", motV), (Name "A", tyA)]) (Pi (Name "a") (Var (Name "A")) (App (var "mot") (Lft (var "a"))))
        areTy = eval (Env [(Name "mot", motV), (Name "B", tyB)]) (Pi (Name "b") (Var (Name "B")) (App (var "mot") (Rght (var "b"))))
    check ctx mot motTy
    check ctx ell ellTy
    check ctx are areTy
    let tgtV = eval (mkEnv ctx) tgt
    return (doApply motV tgtV)
synth _ other =
    failure ("Unable to synthesize a type for " ++ show other)

check :: Ctx -> Expr -> Ty -> Either Message ()
check ctx (Lambda x body) t = do
    (a, b) <- isPi ctx t
    let xV = evalClosure b (VNeutral a (NVar x))
    check (extendCtx ctx x a) body xV
check ctx (Cons a d) t = do
    (aT, dT) <- isSigma ctx t
    check ctx a aT
    let aV = eval (mkEnv ctx) a
    check ctx d (evalClosure dT aV)
check ctx Zero t = isNat ctx t
check ctx (Add1 n) t = do
    isNat ctx t
    check ctx n VNat
check ctx Same t = do
    (t, from, to) <- isEqual ctx t
    convert ctx t from to
check ctx Sole t = isTrivial ctx t
check ctx (Tick _) t = isAtom ctx t
--          Γ ⊢ e ⇐ A
-- -----------------------------
--  Γ ⊢ (left e) ⇐ (Either A B)
check ctx (Lft e) t = do
    (tyA, _) <- isEither ctx t
    check ctx e tyA
--           Γ ⊢ e ⇐ B
-- -----------------------------
--  Γ ⊢ (right e) ⇐ (Either A B)
check ctx (Rght e) t = do
    (_, tyB) <- isEither ctx t
    check ctx e tyB
check ctx other t = do
    t' <- synth ctx other
    convert ctx VU t' t

convert :: Ctx -> Ty -> Value -> Value -> Either Message ()
convert ctx t v1 v2 =
    if alphaEquiv e1 e2
        then return ()
        else failure (show e1 ++ " is not the same as " ++ show e2)
  where
    e1 = readBackTyped ctx t v1
    e2 = readBackTyped ctx t v2

unexpected :: Ctx -> String -> Value -> Either Message a
unexpected ctx msg t = failure (msg ++ ": " ++ show e)
  where
    e = readBackTyped ctx VU t

isPi :: Ctx -> Value -> Either Message (Ty, Closure)
isPi _ (VPi a b) = return (a, b)
isPi ctx other = unexpected ctx "Not a Pi type" other

isSigma :: Ctx -> Value -> Either Message (Ty, Closure)
isSigma _ (VSigma a b) = return (a, b)
isSigma ctx other = unexpected ctx "Not a Sigma type" other

isNat :: Ctx -> Value -> Either Message ()
isNat _ VNat = return ()
isNat ctx other = unexpected ctx "Not Nat" other

isEqual :: Ctx -> Value -> Either Message (Ty, Value, Value)
isEqual _ (VEq ty from to) = return (ty, from, to)
isEqual ctx other = unexpected ctx "Not an equality type" other

isAbsurd :: Ctx -> Value -> Either Message ()
isAbsurd _ VAbsurd = return ()
isAbsurd ctx other = unexpected ctx "Not Absurd: " other

isTrivial :: Ctx -> Value -> Either Message ()
isTrivial _ VTrivial = return ()
isTrivial ctx other = unexpected ctx "Not Trivial" other

isAtom :: Ctx -> Value -> Either Message ()
isAtom _ VAtom = return ()
isAtom ctx other = unexpected ctx "Not Atom" other

isEither :: Ctx -> Value -> Either Message (Ty, Ty)
isEither _ (VEither tyA tyB) = return (tyA, tyB)
isEither ctx other = unexpected ctx "Not Either" other

data Toplevel = Define Name Expr | Example Expr

newtype Output = ExampleOutput Expr
    deriving (Eq, Show)

toplevel :: Ctx -> Toplevel -> Either Message ([Output], Ctx)
toplevel ctx (Define x e) =
    case lookupType ctx x of
        Right _ -> failure ("The name " ++ show x ++ " is already defined.")
        Left _ ->
            do
                t <- synth ctx e
                let v = eval (mkEnv ctx) e
                return ([], define ctx x t v)
toplevel ctx (Example e) =
    do
        t <- synth ctx e
        let v = eval (mkEnv ctx) e
            e' = readBackTyped ctx t v
            t' = readBackTyped ctx VU t
        return ([ExampleOutput (The t' e')], ctx)

processFile :: [Toplevel] -> Either Message ([Output], Ctx)
processFile = process' initCtx
  where
    process' ctx [] = Right ([], ctx)
    process' ctx (t : ts) =
        do
            (out, ctx') <- toplevel ctx t
            (moreOut, ctx'') <- process' ctx' ts
            return (out ++ moreOut, ctx'')

testfile :: [Toplevel] -> Either Message [Output]
testfile decls =
    do
        (out, _) <- processFile decls
        return out

(@@) :: Expr -> Expr -> Expr
(@@) = App
infixl 5 @@

var :: String -> Expr
var s = Var (Name s)

evenOddProgram :: [Toplevel]
evenOddProgram =
    [ Define
        (Name "double")
        ( The
            (Pi (Name "x") Nat Nat)
            ( Lambda
                (Name "x")
                ( IndNat
                    (Var (Name "x"))
                    (Lambda (Name "_") Nat)
                    Zero
                    (Lambda (Name "_") (Lambda (Name "dbl") (Add1 (Add1 (Var (Name "dbl"))))))
                )
            )
        )
    , Example (App (Var (Name "double")) (Add1 (Add1 (Add1 Zero))))
    , Define
        (Name "Even")
        (The
            (Pi (Name "x") Nat U)
            (Lambda
                (Name "n")
                (Sigma
                    (Name "half") Nat
                    (Equal
                        Nat
                        (Var (Name "n"))
                        (App (Var (Name "double")) (Var (Name "half")))))))
    -- , Example (App (Var (Name "Even")) Zero)
    , Define
        (Name "Odd")
        (The
            (Pi (Name "x") Nat U)
            (Lambda
                (Name "n")
                (Sigma
                    (Name "half") Nat
                    (Equal
                        Nat
                        (Var (Name "n"))
                        (Add1 (App (Var (Name "double")) (Var (Name "half"))))))))
    -- , Example (App (Var (Name "Odd")) (Add1 Zero))

    , Define
        (Name "zero-is-even")
        (The
            (App (Var (Name "Even")) Zero)
            (Cons Zero Same))
    , Example (Var (Name "zero-is-even"))

    , Define
        (Name "cong")
        ( The
            ( Pi
                (Name "A")
                U
                ( Pi
                    (Name "B")
                    U
                    ( Pi
                        (Name "from")
                        (Var (Name "A"))
                        ( Pi
                            (Name "to")
                            (Var (Name "A"))
                            ( Pi
                                (Name "eq")
                                (Equal (Var (Name "A")) (Var (Name "from")) (Var (Name "to")))
                                ( Pi
                                    (Name "f")
                                    (Pi (Name "x") (Var (Name "A")) (Var (Name "B")))
                                    ( Equal
                                        (Var (Name "B"))
                                        (App (Var (Name "f")) (Var (Name "from")))
                                        (App (Var (Name "f")) (Var (Name "to")))
                                    )
                                )
                            )
                        )
                    )
                )
            )
            ( Lambda
                (Name "A")
                ( Lambda
                    (Name "B")
                    ( Lambda
                        (Name "from")
                        ( Lambda
                            (Name "to")
                            ( Lambda
                                (Name "eq")
                                ( Lambda
                                    (Name "f")
                                    ( Replace
                                        (Var (Name "eq"))
                                        ( Lambda
                                            (Name "where")
                                            ( Equal
                                                (Var (Name "B"))
                                                (App (Var (Name "f")) (Var (Name "from")))
                                                (App (Var (Name "f")) (Var (Name "where")))
                                            )
                                        )
                                        Same
                                    )
                                )
                            )
                        )
                    )
                )
            )
        )

    , Define
        (Name "add1-even->odd") -- page 273
        (The
            (Pi (Name "n") Nat
                (Pi (Name "x") (var "Even" @@ var "n")
                    (var "Odd" @@ Add1 (var "n"))))
            (Lambda (Name "n")
                (Lambda (Name "en")
                        (Cons
                            (Car (var "en"))
                            (var "cong"
                                @@ Nat
                                @@ Nat
                                @@ var "n"
                                @@ (var "double" @@ Car (var "en"))
                                @@ Cdr (var "en")
                                @@ Lambda (Name "n") (Add1 (var "n")))))))
    , Example (Var (Name "add1-even->odd"))

    , Define
        (Name "add1-odd->even")
        (The
            (Pi (Name "n") Nat
                (Pi (Name "x") (var "Odd" @@ var "n")
                    (var "Even" @@ Add1 (var "n"))))
            (Lambda (Name "n")
                (Lambda (Name "on")
                        (Cons
                            (Add1 (Car (var "on")))
                            (var "cong"
                                @@ Nat
                                @@ Nat
                                @@ var "n"
                                @@ Add1 (var "double" @@ Car (var "on"))
                                @@ Cdr (var "on")
                                @@ Lambda (Name "n") (Add1 (var "n")))))))
    , Example (Var (Name "add1-odd->even"))

    , Define
        (Name "even-or-odd")
        (The
            (Pi (Name "n") Nat
                (Either (var "Even" @@ var "n") (var "Odd" @@ var "n")))
            (Lambda (Name "n")
                (IndNat (var "n")
                    (Lambda (Name "n") $ Either (var "Even" @@ var "n") (var "Odd" @@ var "n"))
                    (Lft (var "zero-is-even"))
                    (Lambda (Name "m")
                        $ Lambda (Name "eo")
                        $ IndEither (var "eo") (Lambda (Name "k") $ Either (var "Even" @@ Add1 (var "m")) (var "Odd" @@ Add1 (var "m")))
                            (Lambda (Name "en") $ Rght $ var "add1-even->odd" @@ var "m" @@ var "en")
                            (Lambda (Name "on") $ Lft $ var "add1-odd->even" @@ var "m" @@ var "on"))))
        )
        -- , Example (Var (Name "even-or-odd"))

        -- You can use these examples to check whether your proof that all
        -- numbers are even or odd returns the expected results.
        , Example (App (Var (Name "even-or-odd")) (Add1 (Add1 (Add1 Zero))))
        , Example (App (Var (Name "even-or-odd")) (App (Var (Name "double")) (Add1 (Add1 (Add1 Zero)))))
    ]

main :: IO ()
main = do
    case testfile evenOddProgram of
        Left err -> print err
        Right r -> for_ r print

