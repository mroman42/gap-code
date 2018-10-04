-- Page 81. Lambek, Scott.

--  a > unit
--  pi1 (pair a b) > a
--  pi2 (pair a b) > b
--  pair (pi1 c) (pi2 c) > c
--  lambda (phi[1]) a > phi[a]
--  lambda (app f 1) > f


data Type = One
          | Times Type Type
          | Arrow Type Type
          | Basic String
          deriving (Show, Eq)

data Exp = Unit
         | Const Type String
         | Var Int
         | Lambda Type Exp
         | App Exp Exp
         | Pair Exp Exp
         | Fst Exp
         | Snd Exp
          deriving (Show, Eq)         


-- Compute the type of an expression
type Ctx = [Type]

typeof :: Exp -> Type
typeof = typeofacc []

typeofacc :: Ctx -> Exp -> Type
typeofacc ctx Unit = One
typeofacc ctx (Const t s) = t
typeofacc ctx (Var n) = ctx !! n
typeofacc ctx (Lambda t a) = Arrow t (typeofacc (t : ctx) a)
typeofacc ctx (App a b) = case typeofacc ctx a of Arrow x y -> case typeofacc ctx b of y -> x
typeofacc ctx (Pair a b) = Times (typeofacc ctx a) (typeofacc ctx b)
typeofacc ctx (Fst a) = case typeofacc ctx a of Times x y -> x
typeofacc ctx (Snd a) = case typeofacc ctx a of Times x y -> y



-- Simplification
simplify :: Ctx -> Exp -> Exp
simplify ctx = stabilizes (recursively ctx . appRule . etaRule . pairRule . sndRule . fstRule . unitRule ctx)
  where
    -- Eta-reduction for the unit type
    -- a > unit
    unitRule :: Ctx -> Exp -> Exp
    unitRule ctx a = if typeofacc ctx a == One then Unit else a

    -- First projection
    --  fst (pair a b) > a
    fstRule :: Exp -> Exp
    fstRule (Fst (Pair a b)) = a
    fstRule x = x

    -- Second projection
    --  snd (pair a b) > b
    sndRule :: Exp -> Exp
    sndRule (Snd (Pair a b)) = b
    sndRule x = x

    -- Pair eta-reduction
    --  pair (pi1 c) (pi2 c) > c
    pairRule :: Exp -> Exp
    pairRule (Pair (Fst x) (Snd y)) = if x == y then x else Pair (Fst x) (Snd y)
    pairRule x = x

    -- Eta-extensionality for functions
    --  lambda (app f 1) > f    
    etaRule :: Exp -> Exp
    etaRule (App f (Var 0)) = f
    etaRule x = x

    -- Function application    
    --  lambda (phi[1]) a > phi[a]    
    appRule :: Exp -> Exp
    appRule (App (Lambda t m) a) = substitute 1 a m
    appRule x = x

    -- Recursively applies substitution
    recursively :: Ctx -> Exp -> Exp
    recursively ctx Unit = Unit
    recursively ctx (Const t s) = Const t s
    recursively ctx (Var m) = Var m
    recursively ctx (Lambda t e) = Lambda t (simplify (t : ctx) e)
    recursively ctx (App a b) = App (simplify ctx a) (simplify ctx b)
    recursively ctx (Pair a b) = Pair (simplify ctx a) (simplify ctx b)
    recursively ctx (Fst a) = Fst (simplify ctx a)
    recursively ctx (Snd a) = Snd (simplify ctx a)

    -- Until it stabilizes
    stabilizes :: (Exp -> Exp) -> Exp -> Exp
    stabilizes p e
      | e == p e  = e
      | otherwise = stabilizes p (p e)
  
substitute :: Int -> Exp -> Exp -> Exp
substitute n x Unit = Unit
substitute n x (Const t s) = Const t s
substitute n x (Var m)
  | n == m = x
  | n <  m = Var (m-1)
  | otherwise = Var m
substitute n x (Lambda t e) = Lambda t (substitute (n+1) (incrFreeVar 0 x) e)
substitute n x (App a b)  = App (substitute n x a) (substitute n x b)
substitute n x (Pair a b) = Pair (substitute n x a) (substitute n x b)
substitute n x (Fst a) = Fst (substitute n x a)
substitute n x (Snd a) = Snd (substitute n x a)

incrFreeVar :: Int -> Exp -> Exp
incrFreeVar n Unit = Unit
incrFreeVar n (Const t s) = Const t s
incrFreeVar n (Var m)
  | m > n = Var (succ m)
  | otherwise = Var m
incrFreeVar n (Lambda t e) = Lambda t (incrFreeVar (succ n) e)
incrFreeVar n (App a b) = App (incrFreeVar n a) (incrFreeVar n b)
incrFreeVar n (Pair a b) = Pair (incrFreeVar n a) (incrFreeVar n b)
incrFreeVar n (Fst a) = Fst (incrFreeVar n a)
incrFreeVar n (Snd a) = Snd (incrFreeVar n a)
