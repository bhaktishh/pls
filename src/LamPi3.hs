module LamPi3 where 

    data Tm = BaseTy String
            | Star 
            | Forall Tm Tm 
            | Var Var 
            | App Tm Tm 
            | Lam Tm Tm 
            deriving (Show, Eq)

    data Var = Bound Int 
            | Free String 
            deriving (Show, Eq)

    data Val = VStar
              | VForall Val (Val -> Val)
              | VLam Val (Val -> Val)
              | VNeut Neut


    data Neut = NVar Var
               | NApp Neut Val
               | NBaseTy Var

    type Env = [Val] -- evaluation environment, variable assignments

    eval :: Tm -> Env -> Val 
    eval (BaseTy t) _ = VNeut (NVar (Free t)) 
    eval Star _ = VStar 
    eval (Forall t t') env = VForall (eval t env) (\x -> eval t' (x : env)) 
    eval (Var (Bound i)) env = env !! i
    eval (Var v) _ = VNeut (NVar v)
    eval (App e e') env = case eval e env of 
        VNeut n -> VNeut (NApp n (eval e' env)) 
        VLam _ f -> f (eval e' env)
        VForall _ f -> f (eval e' env)
        VStar -> error "applying Star"
    eval (Lam t e) env = VLam (eval t env) (\x -> eval e (x : env))

    type Type = Val 
    type Ctx = [(String, Val)] -- typing context 

    fresh :: Ctx -> String 
    fresh ctx = 'x' : concatMap fst ctx

    typeinfer :: Tm -> Ctx -> Either String Type
    typeinfer (BaseTy t) _ = Right VStar  
    typeinfer Star _ = Right VStar 
    typeinfer (Forall p p') ctx = undefined 
    typeinfer (Var (Free v)) ctx = case lookup v ctx of 
        Just t -> Right t
        Nothing -> Left "free variable not in context" 
    typeinfer (Var _) _ = Left "bound variable in typeinfer"
    typeinfer (App e e') ctx = case typeinfer e ctx of 
        Right (VForall t t') -> case typeinfer e' ctx of 
            Right t_ | unify t t_ -> Right $ t' t -- do i need to eval here??
            _ -> Left "could not infer e' in app"
        _ -> Left "ill-typed application"
    typeinfer (Lam p e) ctx = let
        x = fresh ctx
        tm = subst 0 (Var (Free x)) e 
        t = eval p [] in 
            case typeinfer tm ((x, t) : ctx) of 
                Right t' -> Right $ eval (Forall (quote t) (quote t')) []
                _ -> Left "could not infer a type for body of lambda"

    subst :: Int -> Tm -> Tm -> Tm   
    subst i x e = undefined 

    quote :: Val -> Tm 
    quote = undefined 

    unify :: Val -> Val -> Bool
    unify = undefined