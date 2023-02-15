module STLC where

data TermInfer
  = Ann TermCheck Type
  | Bound Int
  | Free Name
  | TermInfer :@: TermCheck
  deriving (Show, Eq)

data TermCheck
  = Inf TermInfer
  | Lam TermCheck
  deriving (Show, Eq)

data Name
  = Global String
  | Local Int
  | Quote Int
  deriving (Show, Eq)

data Type
  = TFree Name
  | Fun Type Type
  deriving (Show, Eq)

data Value
  = VLam (Value -> Value)
  | VNeutral Neutral

instance Show Value where
  show (VLam _) = "<Function>"
  show (VNeutral n) = show n

data Neutral
  = NFree Name
  | NApp Neutral Value
  deriving (Show)

type Env = [Value]

vfree :: Name -> Value
vfree name = VNeutral (NFree name)

vapp :: Value -> Value -> Value
vapp (VLam f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)

evalInfer :: Env -> TermInfer -> Value
evalInfer d (Ann e _) = evalCheck d e
evalInfer d (Bound i) = d !! i
evalInfer d (Free x) = vfree x
evalInfer d (e :@: e') = vapp (evalInfer d e) (evalCheck d e')

evalCheck :: Env -> TermCheck -> Value
evalCheck d (Inf i) = evalInfer d i
evalCheck d (Lam e) = VLam (\x -> evalCheck (x : d) e)

data Kind = Star
  deriving (Show)

data Info
  = HasKind Kind
  | HasType Type
  deriving (Show)

quote0 :: Value -> TermCheck
quote0 = quote 0

quote :: Int -> Value -> TermCheck
quote i (VLam f) = Lam (quote (i + 1) (f (vfree (Quote i))))
quote i (VNeutral n) = Inf (neutralQuote i n)

neutralQuote :: Int -> Neutral -> TermInfer
neutralQuote i (NFree x) = boundfree i x
neutralQuote i (NApp n v) = neutralQuote i n :@: quote i v

boundfree :: Int -> Name -> TermInfer
boundfree i (Quote k) = Bound (i - k - 1)
boundfree i x = Free x

type Context = [(Name, Info)]

type Result a = Either String a

failure :: String -> Result a
failure = Left

kindCheck :: Context -> Type -> Kind -> Result ()
kindCheck g (TFree x) Star =
  case lookup x g of
    Just (HasKind Star) -> return ()
    Just (HasType t) -> failure ("Checking for kind of `" ++ show x ++ "`, but it's a term of type `" ++ show t ++ "`.")
    Nothing -> failure ("Checking for kind of `" ++ show x ++ "`, but it doesn't exist in the context.")
kindCheck g (Fun k k') Star =
  do
    kindCheck g k Star
    kindCheck g k' Star

typeInfer0 :: Context -> TermInfer -> Result Type
typeInfer0 = typeInfer 0

typeInfer :: Int -> Context -> TermInfer -> Result Type
typeInfer i g (Ann e t) =
  do
    kindCheck g t Star
    typeCheck i g e t
    return t
typeInfer i g (Bound j) = undefined "typeInfer for bound variables is undefined (??)"
typeInfer i g (Free x) =
  case lookup x g of
    Just (HasType t) -> return t
    Just (HasKind Star) -> failure ("Inferring type of `" ++ show x ++ "`, but it's a type of kind `" ++ show Star ++ "`.")
    Nothing -> failure ("Inferring type of `" ++ show x ++ "`, but it doesn't exist in the context.")
typeInfer i g (e :@: e') =
  do
    s <- typeInfer i g e
    case s of
      Fun t t' -> do
        typeCheck i g e' t
        return t'
      _ -> failure ("Inferring type of `" ++ show e ++ "` applied to `" ++ show e' ++ "`, but the former isn't a function.")

typeCheck :: Int -> Context -> TermCheck -> Type -> Result ()
typeCheck i g (Inf e) t =
  do
    t' <- typeInfer i g e
    if t == t'
      then return ()
      else
        failure
          ( "Checking type of `"
              ++ show e
              ++ "`, but it's inferred type `"
              ++ show t'
              ++ "` does not match the checked type `"
              ++ show t
              ++ "`."
          )
typeCheck i g (Lam e) (Fun t t') =
  typeCheck
    (i + 1)
    ((Local i, HasType t) : g)
    (substCheck 0 (Free (Local i)) e)
    t'
typeCheck i g e t = failure ("Checking type of `" ++ show e ++ "`, but it's not the type `" ++ show t ++ "`.")

substInfer :: Int -> TermInfer -> TermInfer -> TermInfer
substInfer i r (Ann e t) = Ann (substCheck i r e) t
substInfer i r (Bound j) = if i == j then r else Bound j
substInfer i r (Free x) = Free x
substInfer i r (e :@: e') = substInfer i r e :@: substCheck i r e'

substCheck :: Int -> TermInfer -> TermCheck -> TermCheck
substCheck i r (Inf e) = Inf (substInfer i r e)
substCheck i r (Lam e) = Lam (substCheck (i + 1) r e)