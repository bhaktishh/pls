{-# LANGUAGE TypeFamilies #-}
module LamPiHoasReal where
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
    import Text.Megaparsec
    import Data.Functor (($>))
    import Text.Megaparsec.Char (char, string, lowerChar, upperChar, alphaNumChar, space)

    -- parser

    data PTerm = PStar
                | PVar String
                | PApp PTerm PTerm
                | PLam String PTerm PTerm
                | PForall String PTerm PTerm
                | PType String
                deriving (Show, Eq)

    type Parser = Parsec Void String
    
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

    pKWForall :: Parser ()
    pKWForall = string "forall" $> ()

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
        _ <- pSpaces pKWForall
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
            | Forall Term Term 
            | Var Var 
            | App Term Term 
            | Lam Term Term 
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

    eval :: Term -> Env -> Val 
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

    type Tcm a = Either String a

    subst :: Int -> Term -> Term -> Term   
    subst i x (Var (Bound j)) = if i == j then x else Var (Bound j)
    subst i x (App e1 e2) = App (subst i x e1) (subst i x e2)
    subst i x (Lam t e) = Lam (subst i x t) (subst (i+1) x e)
    subst i x (Forall t t') = Forall (subst i x t) (subst (i+1) x t')
    subst _ _ x = x

    quote :: Val -> Term 
    quote = quote_ 0

    quote_ :: Int -> Val -> Term
    quote_ _ VStar = Star
    quote_ i (VForall x f) = Forall (quote_ i x) (quote_ (i+1) (f (VNeut (NVar (Bound i)))))
    quote_ i (VLam x f) = Lam (quote_ i x) (quote_ (i+1) (f (VNeut (NVar (Bound i)))))
    quote_ i (VNeut n) = quoteNeutral i n 

    quoteNeutral :: Int -> Neut -> Term
    quoteNeutral _ (NBaseTy str) = BaseTy str 
    quoteNeutral i (NApp n v) = App (quoteNeutral i n) (quote_ i v)
    quoteNeutral i (NVar (Quote x)) = Var (Bound (i - x - 1)) 
    quoteNeutral _ (NVar x) = Var x

    unify :: Val -> Val -> Bool
    unify a b = quote a == quote b

    typeinfer :: PTerm -> Ctx -> Tcm Type 
    typeinfer PStar _ = Right VStar  
    typeinfer (PApp a b) ctx = undefined 
    typeinfer (PVar x) ctx = undefined 
    typeinfer (PLam l x t) ctx = undefined 
    typeinfer (PForall l x t) ctx = undefined 
    typeinfer (PType x) ctx = undefined 
