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

    type Ctx = [(String, Val)]

    fresh :: [String] -> String 
    fresh xs = 'x' : concat xs

    typeinfer :: Expr -> Ctx -> Either String Val 
    typeinfer Star _ = Right VStar
    typeinfer (Var (Free str)) ctx = case lookup str ctx of
        Just v -> Right v 
        _ -> Left "var not in context"
    typeinfer (Var _) _= Left ":("
    typeinfer (Forall e e') ctx = case typeinfer e ctx of 
        Right VStar -> 
            let t = eval e []
                var = fresh (map fst ctx) in
                    typeinfer (subst 0 (Var (Free var)) e') ((var, t) : ctx)
        _ -> Left "dependent var not type"
    typeinfer (Lam t_ e) ctx = let var = fresh (map fst ctx) 
                                   t = eval t_ [] in 
        case typeinfer (subst 0 (Var (Free var)) e) ((var, t) : ctx) of 
            Right t' -> Right (VForall t t')
            _ -> Left "could not check lambda"
    typeinfer (App e e') ctx = case typeinfer e ctx of
        Right (VForall t t') -> if typeinfer e' ctx == Right t then Right (t' t) else Left "??"
        _ -> Left "??"

    -- typeinfer :: Expr -> Ctx -> Either String Ty
    -- typeinfer (Var (Free str)) ctx = case lookup str ctx of
    --     Just (HasType ty) -> Right ty
    --     _ -> Left "variable not in context"
    -- typeinfer (Var _) _ = Left "bound variable in typecheck" -- bruh TODO 
    -- typeinfer (App e1 e2) ctx = case typeinfer e1 ctx of
    --     Right (Func t1 t2) -> case typeinfer e2 ctx of
    --         Right t1' -> if t1 == t1' then Right t2 else Left "ill-typed application"
    --         _ -> Left "could not infer apply arg"
    --     _ -> Left "ill typed app"
    -- typeinfer (Lam ty e) ctx = let var = fresh (map fst ctx) in
    --     case typeinfer (subst 0 (Var (Free var)) e) ((var, HasType ty) : ctx) of
    --         Right ty' -> Right (Func ty ty')
    --         _ -> Left "function body could not be typed"

    -- typecheck :: Expr -> Ctx -> Either String Ty
    -- typecheck expr ctx = do
    --     t <- typeinfer expr ctx
    --     _ <- isType t ctx
    --     Right t

    subst :: Int -> Expr -> Expr -> Expr
    subst i e (Var (Bound i')) = if i == i' then e else Var (Bound i')
    subst _ _ (Var x) = Var x
    subst i e (App e1 e2) = App (subst i e e1) (subst i e e2)
    subst i e (Lam ty e') = Lam ty (subst (i+1) e e')

    -- quote :: Val -> Expr
    -- quote = quote_ 0

    -- quote_ :: Int -> Val -> Expr 
    -- quote_ i (VNeut n) = quoteNeutral i n
    -- quote_ i (VLam ty f) = 
    --     let e = quote_ (i+1) (f (VNeut (NVar (Quote i)))) in
    --         Lam ty e

    -- quoteNeutral :: Int -> Neut -> Expr 
    -- quoteNeutral i (NVar v) = conv i v 
    -- quoteNeutral i (NApp n v) = App (quoteNeutral i n) (quote_ i v)

    -- conv :: Int -> Var -> Expr 
    -- conv i (Quote i') = Var (Bound (i - i' - 1))
    -- conv _ x = Var x
