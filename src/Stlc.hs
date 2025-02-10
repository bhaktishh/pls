module Stlc () where
    -- import Text.Megaparsec ( Parsec )
    -- import Data.Void
    -- import Data.Text (Text)
    -- import qualified Data.Text as T
    -- import Text.Megaparsec.Char
    data Expr = Var Var
                | App Expr Expr
                | Lam Ty Expr
                deriving (Show, Eq)

    data Ty = Base String
            | Func Ty Ty
            deriving (Show, Eq)

    data Var = Bound Int
            | Free String
            | Quote Int
            deriving (Show, Eq)

    data Val = VLam Ty (Val -> Val)
            | VNeut Neut

    data Neut = NVar Var
            | NApp Neut Val

    type Env = [Val]

    eval :: Expr -> Env -> Val
    eval (Var (Bound i)) env = env !! i
    eval (Var v) _ = VNeut (NVar v)
    eval (App e1 e2) env = case eval e1 env of
        VLam _ f -> f (eval e2 env)
        VNeut n -> VNeut (NApp n (eval e2 env))
    eval (Lam ty e) env = VLam ty (\x -> eval e (x : env))

    data TypeOrKind = HasType Ty
                    | HasKind

    type Ctx = [(String, TypeOrKind)]

    fresh :: [String] -> String
    fresh xs = 'x' : concat xs

    isType :: Ty -> Ctx -> Either String ()
    isType (Base str) ctx = case lookup str ctx of
        Just HasKind -> Right ()
        _ -> Left "not a type"
    isType (Func t1 t2) ctx = isType t1 ctx >> isType t2 ctx

    typeinfer :: Expr -> Ctx -> Either String Ty
    typeinfer (Var (Free str)) ctx = case lookup str ctx of
        Just (HasType ty) -> Right ty
        _ -> Left "variable not in context"
    typeinfer (Var _) _ = Left "bound variable in typecheck" 
    typeinfer (App e1 e2) ctx = case typeinfer e1 ctx of
        Right (Func t1 t2) -> case typeinfer e2 ctx of
            Right t1' -> if t1 == t1' then Right t2 else Left "ill-typed application"
            _ -> Left "could not infer apply arg"
        _ -> Left "ill typed app"
    typeinfer (Lam ty e) ctx = let var = fresh (map fst ctx) in
        case typeinfer (subst 0 (Var (Free var)) e) ((var, HasType ty) : ctx) of
            Right ty' -> Right (Func ty ty')
            _ -> Left "function body could not be typed"

    typecheck :: Expr -> Ctx -> Either String Ty
    typecheck expr ctx = do
        t <- typeinfer expr ctx
        _ <- isType t ctx
        Right t

    subst :: Int -> Expr -> Expr -> Expr
    subst i e (Var (Bound i')) = if i == i' then e else Var (Bound i')
    subst _ _ (Var x) = Var x
    subst i e (App e1 e2) = App (subst i e e1) (subst i e e2)
    subst i e (Lam ty e') = Lam ty (subst (i+1) e e')

    quote :: Val -> Expr
    quote = quote_ 0

    quote_ :: Int -> Val -> Expr
    quote_ i (VNeut n) = quoteNeutral i n
    quote_ i (VLam ty f) =
        let e = quote_ (i+1) (f (VNeut (NVar (Quote i)))) in
            Lam ty e

    quoteNeutral :: Int -> Neut -> Expr
    quoteNeutral i (NVar v) = conv i v
    quoteNeutral i (NApp n v) = App (quoteNeutral i n) (quote_ i v)

    conv :: Int -> Var -> Expr
    conv i (Quote i') = Var (Bound (i - i' - 1))
    conv _ x = Var x


    id' :: Expr
    id' = Lam (Base "int") (Var (Bound 0))

    const' :: Expr
    const' = Lam (Func (Base "int") (Base "int")) (Lam (Base "int") (Var (Bound 1)))