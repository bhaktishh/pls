module LamPi where 

    data Expr = Var Var
                | App Expr Expr 
                | Lam Expr Expr 
                | Forall Expr Expr -- type const
                | Star
                deriving (Show, Eq)
    
    data Var = Bound Int 
              | Free String 
              | Quote Int 
              deriving (Show, Eq)

    data Val = VNeut Neut
               | VStar 
               | VForall Val (Val -> Val) -- type const 
               | VLam Val (Val -> Val)

    data Neut = NVar Var 
                | NApp Neut Val

    type Env = [Val]

    eval :: Expr -> Env -> Val
    eval (Var (Bound i)) env = env !! i 
    eval (Var v) _ = VNeut (NVar v)
    eval Star _ = VStar
    eval (Forall e1 e2) env = VForall (eval e1 env) (\x -> eval e2 (x : env))
    eval (App e1 e2) env = case eval e1 env of 
        VLam _ f -> f (eval e2 env)
        VNeut n -> VNeut (NApp n (eval e2 env))
        _ -> undefined
    eval (Lam ty e) env = VLam (eval ty env) (\x -> eval e (x : env))

    type Ctx = [Val]

    typecheck :: Expr -> Ctx -> Either String Expr 
    typecheck expr ctx = do 
        t <- typeinfer expr ctx 
        Right (quote t)

    typeinfer :: Expr -> Ctx -> Either String Val 
    typeinfer Star _ = Right VStar
    typeinfer (Var (Bound i)) ctx = Right (ctx !! i)
    typeinfer (Var _) _= Left ":("
    typeinfer (Forall e e') ctx = case typeinfer e ctx of 
        Right VStar -> 
            let t = eval e ctx in
                typeinfer e' (t : ctx) -- todo 
        _ -> Left "dependent var not type"
    typeinfer (Lam t_ e) ctx = do 
        let t = eval t_ ctx
        tbody <- typeinfer e (t : ctx)
        let qbody = quote tbody in 
            Right $ eval (Forall (quote t) qbody) ctx
    typeinfer (App e e') ctx = case typeinfer e ctx of
        Right (VForall t t') -> case typeinfer e' ctx of
            Right t_ | quote t == quote t_ -> Right $ eval (quote (t' t)) ctx -- do we need some fancier unification here???
            _ -> Left ":(("
        _ -> Left "h"

    quote :: Val -> Expr
    quote = quote_ 0 

    quote_ :: Int -> Val -> Expr
    quote_ _ VStar = Star
    quote_ i (VNeut n) = quoteNeutral i n
    quote_ i (VLam t f) = Lam (quote_ i t) (quote_ (i + 1) (f t))
    quote_ i (VForall t f) = Forall (quote_ i t) (quote_ (i + 1) (f t))

    quoteNeutral :: Int -> Neut -> Expr 
    quoteNeutral i (NVar (Quote i')) = Var (Bound (i - i' - 1))
    quoteNeutral _ (NVar v) = Var v
    quoteNeutral i (NApp n v) = App (quoteNeutral i n) (quote_ i v)