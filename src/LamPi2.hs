{-# LANGUAGE BlockArguments #-}
module LamPi2 where

    data Ty = BaseTy Var
             | Star 
             | Forall Ty Ty 
            deriving (Show, Eq)

    data Tm = Ty Ty 
            | Var Var 
            | App Tm Tm 
            | Lam Ty Tm 
            deriving (Show, Eq)

    data Var = Bound Int
            | Free String 
            deriving (Show, Eq)

    data Val = VTy VTy
              | VLam VTy (Val -> Val)
              | VNeut Neut

    data Neut = NVar Var
               | NTy NeutTy
               | NApp Neut Val

    data VTy = VStar
                | VForall VTy (Val -> VTy)
                | VNeutTy NeutTy

    data NeutTy = NBaseTy Var
                | NTyApp NeutTy Val 


    type Env = [Val] -- variable assignments

    evalTy :: Ty -> Env -> VTy
    evalTy Star _ = VStar
    evalTy (BaseTy (Bound i)) env = case env !! i of 
        VTy vt -> vt 
        _ -> error "not a type"
    evalTy (BaseTy v) _ = VNeutTy (NBaseTy v)
    evalTy (Forall t t') env = VForall (evalTy t env) (\x -> evalTy t' (x : env))

    eval :: Tm -> Env -> Val 
    eval (Ty t) env = VTy $ evalTy t env
    eval (Var (Bound i)) env = env !! i
    eval (Var v) _ = VNeut (NVar v)
    eval (App e e') env = case eval e env of 
        VLam _ f -> f (eval e' env)
        VTy (VForall _ f) -> VTy $ f (eval e' env)
        VNeut n -> VNeut $ NApp n (eval e' env)
        VTy (VNeutTy n) -> VNeut $ NApp (NTy n) (eval e' env)
        _ -> error "undefined application"
    eval (Lam t e) env = VLam (evalTy t env) (\x -> eval e (x : env))

    type Ctx = [(String, Ty)] -- typing context

    fresh :: [(String, Ty)] -> String
    fresh xs = 'x' : concatMap fst xs

    typeinfer :: Tm -> Ctx -> Either String Ty 
    typeinfer (Ty t) ctx = typeinferTy t ctx
    typeinfer (Var (Free fv)) ctx = case lookup fv ctx of 
        Just ty -> Right ty
        _ -> Left "free variable not in context"
    typeinfer (Var _) _ = error "bound var in typeinfer"
    typeinfer (App e e') ctx = case typeinfer e ctx of
        Right (Forall t1 t2) -> case typeinfer e' ctx of 
            Right t1' | unify t1 t1' -> Right $ tmToTy . quote $ eval (App (Ty t2) e') []
            _ -> error "could not unify types in app"
        _ -> error "ill-typed application"
    typeinfer (Lam t e) ctx = let var = fresh ctx in 
        case typeinfer (subst 0 (Var (Free var)) e) ((var, t) : ctx) of 
            Right t' -> Right (Forall t t')
            _ -> error "nah"

    typeinferTy :: Ty -> Ctx -> Either String Ty
    typeinferTy Star _ = Right Star
    typeinferTy (BaseTy v) _ = Right (BaseTy v) -- todo
    typeinferTy (Forall p p') ctx = case typeinferTy p ctx of 
        Right Star -> let
            t = evalTy p []
            x = fresh ctx in 
                case typeinferTy (substTy 0 (Var (Free x)) p')
    -- typeinferTy (Forall p p') ctx = case typeinferTy p ctx of 
    --     Right Star -> case evalTy p [] of
    --         t -> let var = fresh ctx in 
    --                 case typeinferTy (tmToTy $ subst 0 (Var (Free var)) t) ((var, t) : ctx) of 
    --                     Right Star -> Right Star
    --                     _ -> error " "
    --     _ -> error " "

    tmToTy :: Tm -> Ty
    tmToTy (Ty t) = t
    tmToTy _ = error "undefined"

    quote :: Val -> Tm
    quote (VTy vt) = Ty $ quoteTy vt
    quote (VLam t f) = undefined 

    quote _ = undefined 

    quoteTy :: VTy -> Ty 
    quoteTy = undefined
 
    unify :: Ty -> Ty -> Bool 
    unify t1 t2 = quoteTy (evalTy t1 []) == quoteTy (evalTy t2 [])

    subst :: Int -> Tm -> Tm -> Tm 
    subst = undefined  