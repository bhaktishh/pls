module LamPiHoas (eval, typeinfer) where 


    {-
        concrete syntax: 

        Terms:
            a, A, b, B := * (Star)
                        | \ (x : A) -> a (Lam)
                        | a b (App)
                        | forall (x : A) -> B (Forall)
                        | x (Variable - lowercase)
                        | A (BaseType - uppercase)

    -}

    import Text.Megaparsec (Parsec, many, notFollowedBy)
    import Data.Void (Void)
    import Data.Functor (($>))
    import Text.Megaparsec.Char (char, string, lowerChar, upperChar, alphaNumChar)
    import Control.Applicative ((<|>))
    
    data Tm = BaseTy String
            | Star 
            | Forall Tm Tm 
            | Var Var 
            | App Tm Tm 
            | Lam Tm Tm 
            deriving (Show, Eq)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        
    data Var = Bound Int 
            | Free String
            | Quote Int
            deriving (Show, Eq)

    data Val = VStar
              | VForall Val (Val -> Val)
              | VLam Val (Val -> Val)
              | VNeut Neut


    data Neut = NVar Var
               | NApp Neut Val
               | NBaseTy String

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

    type Tcm a = Either String a

    typeinfer :: Tm -> Ctx -> Tcm Type
    typeinfer (BaseTy _) _ = Right VStar  
    typeinfer Star _ = Right VStar 
    typeinfer (Forall p p') ctx = case typeinfer p ctx of 
        Right VStar -> let
            t = eval p []
            x = fresh ctx
            p'' = subst 0 (Var (Free x)) p' in 
                case typeinfer p'' ((x, t) : ctx) of
                    Right VStar -> Right VStar
                    _ -> Left "could not infer a type for body of forall"
        _ -> Left "could not infer a type for argument of forall"
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
    subst i x (Var (Bound j)) = if i == j then x else Var (Bound j)
    subst i x (App e1 e2) = App (subst i x e1) (subst i x e2)
    subst i x (Lam t e) = Lam (subst i x t) (subst (i+1) x e)
    subst i x (Forall t t') = Forall (subst i x t) (subst (i+1) x t')
    subst _ _ x = x

    quote :: Val -> Tm 
    quote = quote_ 0

    quote_ :: Int -> Val -> Tm
    quote_ _ VStar = Star
    quote_ i (VForall x f) = Forall (quote_ i x) (quote_ (i+1) (f (VNeut (NVar (Bound i)))))
    quote_ i (VLam x f) = Lam (quote_ i x) (quote_ (i+1) (f (VNeut (NVar (Bound i)))))
    quote_ i (VNeut n) = quoteNeutral i n 

    quoteNeutral :: Int -> Neut -> Tm
    quoteNeutral _ (NBaseTy str) = BaseTy str 
    quoteNeutral i (NApp n v) = App (quoteNeutral i n) (quote_ i v)
    quoteNeutral i (NVar (Quote x)) = Var (Bound (i - x - 1)) 
    quoteNeutral _ (NVar x) = Var x

    unify :: Val -> Val -> Bool
    unify a b = quote a == quote b

-- parser


    data PTerm = PStar 
                | PVar String 
                | PApp PTerm PTerm
                | PLam String PTerm PTerm 
                | PForall String PTerm PTerm 
                | PType String

    type Parser = Parsec Void String 

    pStar :: Parser Tm
    pStar = char '*' $> Star 


    pVar :: Parser PTerm
    pVar = (PVar .) . (:) <$> lowerChar <*> many alphaNumChar

    pType :: Parser PTerm 
    pType = (PType .) . (:) <$> upperChar <*> many alphaNumChar  

    pArrow :: Parser ()
    pArrow = string "->" $> ()


    pForallKW :: Parser ()
    pForallKW = string "forall" <* notFollowedBy alphaNumChar $> () 

    pLam :: Parser Tm 
    pLam = undefined 

    pTerm :: Parser Tm 
    pTerm = 
        pStar
        <|> pLam 
        <|> undefined 