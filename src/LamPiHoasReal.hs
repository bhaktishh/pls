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