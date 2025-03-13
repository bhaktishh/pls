module LamPiHoasRealNat where
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

    import Data.Void
    import Text.Megaparsec ( (<|>), many, Parsec, MonadParsec(try, eof), parse )
    import Data.Functor (($>))
    import Text.Megaparsec.Char (char, string, lowerChar, upperChar, alphaNumChar, space)
    import Data.List (elemIndex) 
    
    -- parser

    data PTerm = PStar
                | PVar String
                | PApp PTerm PTerm
                | PLam String PTerm PTerm
                | PForall String PTerm PTerm
                | PType String
                deriving (Show, Eq)

    type Parser = Parsec Void String

    tmParse :: String -> Tcm PTerm
    tmParse str = case parse pTerm "" str of 
        Left _ -> Left "parser error"
        Right tm -> Right tm 
    
    pSpaces :: Parser a -> Parser a 
    pSpaces p = space *> p <* space

    pParens :: Parser a -> Parser a 
    pParens p = char '(' *> pSpaces p <* char ')'

    pStar :: Parser PTerm
    pStar = char '*' $> PStar

    pVarStr :: Parser String
    pVarStr = (:) <$> lowerChar <*> many alphaNumChar

    pVar :: Parser PTerm
    pVar = PVar <$> pVarStr

    pType :: Parser PTerm
    pType = (PType .) . (:) <$> upperChar <*> many alphaNumChar

    pArrow :: Parser ()
    pArrow = string "->" $> ()

    pTerm :: Parser PTerm 
    pTerm = pTerm0 <* eof 

    pTerm0 :: Parser PTerm
    pTerm0 = try pApp <|> pLam <|> pForall <|> pTerm1 

    pTerm1 :: Parser PTerm 
    pTerm1 = pVar <|> pStar <|> pParens pTerm0

    pApp :: Parser PTerm
    pApp = PApp <$> pSpaces pTerm1 <*> pSpaces pTerm0

    pLam :: Parser PTerm
    pLam = do
        _ <- pSpaces $ char '\\'
        _ <- pSpaces $ char '('
        vname <- pSpaces pVarStr
        _ <- pSpaces $ char ':'
        ty <- pSpaces pType
        _ <- pSpaces $ char ')'
        _ <- pSpaces pArrow
        PLam vname ty <$> pTerm1

    pForall :: Parser PTerm
    pForall = do
        _ <- pSpaces $ string "forall"
        _ <- pSpaces $ char '('
        vname <- pSpaces pVarStr
        _ <- pSpaces $ char ':'
        ty <- pSpaces pType
        _ <- pSpaces $ char ')'
        _ <- pSpaces pArrow
        PForall vname ty <$> pTerm1

-- lang 

    data Term = BaseTy String
            | Star 
            | Forall String Term Term 
            | Var Var 
            | App Term Term 
            | Lam String Term Term 
            | TyNat 
            | CZero
            | CSucc Term 
            | NatElim Term Term Term Term 
            deriving (Show, Eq)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   
    data Var = Bound Int 
            | Free String
            | Quote Int
            deriving (Show, Eq)

    data Val = VStar
              | VForall String Val (Val -> Val)
              | VLam String Val (Val -> Val)
              | VNeut Neut
              | VNat 
              | VZero 
              | VSucc Val 


    data Neut = NVar Var
               | NApp Neut Val
               | NBaseTy String
               | NNatElim Val Val Val Neut

    type Env = [Val] -- evaluation environment, variable assignments

    eval :: Term -> Env -> Val 
    eval (BaseTy t) _ = VNeut (NVar (Free t)) 
    eval Star _ = VStar 
    eval (Forall n t t') env = VForall n (eval t env) (\x -> eval t' (x : env)) 
    eval (Var (Bound i)) env = env !! i
    eval (Var v) _ = VNeut (NVar v)
    eval (App e e') env = case eval e env of 
        VNeut n -> VNeut (NApp n (eval e' env)) 
        VLam _ _ f -> f (eval e' env)
        VForall _ _ f -> f (eval e' env)
        VStar -> error "applying Star"
    eval (Lam n t e) env = VLam n (eval t env) (\x -> eval e (x : env))
    eval TyNat _ = VNat 
    eval CZero _ = VZero 
    eval (CSucc n) env = VSucc (eval n env)
    eval (NatElim m mz ms k) env = case eval k env of
        VZero -> eval mz env 
        VSucc l -> undefined -- vapp alternative -- or should i just get it lol 



    type Type = Val 
    type Ctx = [(String, Val)] -- typing context

    type Tcm a = Either String a

    subst :: Int -> Term -> Term -> Term   
    subst i x (Var (Bound j)) = if i == j then x else Var (Bound j)
    subst i x (App e1 e2) = App (subst i x e1) (subst i x e2)
    subst i x (Lam n t e) = Lam n (subst i x t) (subst (i+1) x e)
    subst i x (Forall n t t') = Forall n (subst i x t) (subst (i+1) x t')
    subst _ _ x = x

    quote :: Val -> Term 
    quote = quote_ 0

    quote_ :: Int -> Val -> Term
    quote_ _ VStar = Star
    quote_ i (VForall n x f) = Forall n (quote_ i x) (quote_ (i+1) (f (VNeut (NVar (Bound i)))))
    quote_ i (VLam n x f) = Lam n (quote_ i x) (quote_ (i+1) (f (VNeut (NVar (Bound i)))))
    quote_ i (VNeut n) = quoteNeutral i n 

    quoteNeutral :: Int -> Neut -> Term
    quoteNeutral _ (NBaseTy str) = BaseTy str 
    quoteNeutral i (NApp n v) = App (quoteNeutral i n) (quote_ i v)
    quoteNeutral i (NVar (Quote x)) = Var (Bound (i - x - 1)) 
    quoteNeutral _ (NVar x) = Var x

    unify :: Val -> Val -> Bool
    unify a b = quote a == quote b

    pTermToTerm :: PTerm -> [String] -> Term
    pTermToTerm PStar _ = Star
    pTermToTerm (PApp a b) ctx = App (pTermToTerm a ctx) (pTermToTerm b ctx)
    pTermToTerm (PVar str) ctx = case elemIndex str ctx of 
        Just i -> Var (Bound i)
        Nothing -> Var (Free str)
    pTermToTerm (PType str) _ = BaseTy str
    pTermToTerm (PForall str t1 t2) ctx = Forall str (pTermToTerm t1 ctx) (pTermToTerm t2 (str : ctx))
    pTermToTerm (PLam str t1 t2) ctx = Lam str (pTermToTerm t1 ctx) (pTermToTerm t2 (str : ctx))

    typeinfer :: Term -> Ctx -> Tcm Type
    typeinfer (BaseTy _) _ = Right VStar  
    typeinfer Star _ = Right VStar 
    typeinfer (Forall x p p') ctx = case typeinfer p ctx of 
        Right VStar -> let
            t = eval p []
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
        Right (VForall n t t') -> case typeinfer e' ctx of 
            Right t_ | unify t t_ -> Right $ t' t -- do i need to eval here??
            _ -> Left "could not infer e' in app"
        _ -> Left "ill-typed application"
    typeinfer (Lam x p e) ctx = let
        tm = subst 0 (Var (Free x)) e 
        t = eval p [] in 
            case typeinfer tm ((x, t) : ctx) of 
                Right t' -> Right $ eval (Forall x (quote t) (quote t')) []
                _ -> Left "could not infer a type for body of lambda"

    process :: String -> Tcm (Val, Type) 
    process str = do
        ptm <- tmParse str 
        let tm = pTermToTerm ptm []
        ty <- typeinfer tm  []
        let val = eval tm [] 
        pure (val, ty)

    main :: IO () 
    main = do 
        inp <- getLine 
        case process inp of 
            Left err -> print err 
            Right (val, ty) -> do
                print (quote val)
                print (quote ty)
                pure () 