module DTLC where

data TermInfer
  = Ann TermCheck TermCheck
  | Star
  | Pi TermCheck TermCheck
  | Bound Int
  | Free Name
  | TermInfer :@: TermCheck
  deriving (Show, Eq)

data TermCheck
  = Inf TermInfer
  | Lam TermCheck
  deriving (Show, Eq)

iAnn t t' = Inf (Ann t t')
iStar = Inf Star
iPi t t' = Inf (Pi t t')
iBound = Inf . Bound
iFree = Inf . Free
-- (@:) f  v = Inf (f :@: Inf v)

data Name
  = Global String
  | Local Int
  | Quote Int
  deriving (Show, Eq)

-- type Type = Value

data Value
  = VLam (Value -> Value)
  | VStar
  | VPi Value (Value -> Value)
  | VNeutral Neutral

instance Show Value where
  show v = "(evalInfer [] (" ++ show (quote0 v) ++ "))"

-- show (VLam _) = "VLam <Function>"
-- show VStar = "VStar"
-- show (VPi v f) = "VPi " ++ show v ++ " <Function>"
-- show (VNeutral n) = "VNeutral " ++ show n

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
vapp _ _ = error "vapp is not defined for `VStar` or `VPi` (??)"

evalInfer :: Env -> TermInfer -> Value
evalInfer d (Ann e _) = evalCheck d e
evalInfer d (Bound i) = d !! i
evalInfer d (Free x) = vfree x
evalInfer d (e :@: e') = vapp (evalInfer d e) (evalCheck d e')
evalInfer d Star = VStar
evalInfer d (Pi t t') = VPi (evalCheck d t) (\x -> evalCheck (x : d) t')

evalCheck :: Env -> TermCheck -> Value
evalCheck d (Inf i) = evalInfer d i
evalCheck d (Lam e) = VLam (\x -> evalCheck (x : d) e)

quote0 :: Value -> TermCheck
quote0 = quote 0

quote :: Int -> Value -> TermCheck
quote i (VLam f) = Lam (quote (i + 1) (f (vfree (Quote i))))
quote i (VNeutral n) = Inf (neutralQuote i n)
quote i VStar = Inf Star
quote i (VPi v f) = Inf (Pi (quote i v) (quote (i + 1) (f (vfree (Quote i)))))

neutralQuote :: Int -> Neutral -> TermInfer
neutralQuote i (NFree x) = boundfree i x
neutralQuote i (NApp n v) = neutralQuote i n :@: quote i v

boundfree :: Int -> Name -> TermInfer
boundfree i (Quote k) = Bound (i - k - 1)
boundfree i x = Free x

type Context = [(Name, Value)]

type Result a = Either String a

failure :: String -> Result a
failure = Left

-- kindCheck :: Context -> Type -> Kind -> Result ()
-- kindCheck g (TFree x) Star =
--   case lookup x g of
--     Just (HasKind Star) -> return ()
--     Just (HasType t) -> failure ("Checking for kind of `" ++ show x ++ "`, but it's a term of type `" ++ show t ++ "`.")
--     Nothing -> failure ("Checking for kind of `" ++ show x ++ "`, but it doesn't exist in the context.")
-- kindCheck g (Fun k k') Star =
--   do
--     kindCheck g k Star
--     kindCheck g k' Star

typeInfer0 :: Context -> TermInfer -> Result Value
typeInfer0 = typeInfer 0

typeInfer :: Int -> Context -> TermInfer -> Result Value
typeInfer i g (Ann e r) =
  do
    typeCheck i g r VStar
    let t = evalCheck [] r
    typeCheck i g e t
    return t
typeInfer i g (Bound j) = failure ("Trying to infer type of bound variable `" ++ show j ++ "`, but we can't do that.")
typeInfer i g (Free x) =
  case lookup x g of
    Just t -> return t
    Nothing -> failure ("Inferring type of `" ++ show x ++ "`, but it doesn't exist in the context `" ++ show g ++ "`")
typeInfer i g (e :@: e') =
  do
    s <- typeInfer i g e
    case s of
      VPi t t' -> do
        typeCheck i g e' t
        return (t' (evalCheck [] e'))
      _ -> failure ("Inferring type of `" ++ show e ++ "` of type `" ++ show s ++ "`, applied to `" ++ show e' ++ "`, but the former isn't a function.")
typeInfer i g Star = return VStar
typeInfer i g (Pi r r') =
  do
    typeCheck i g r VStar
    let t = evalCheck [] r
    typeCheck (i + 1) ((Local i, t) : g) (substCheck0 (Free (Local i)) r') VStar
    return VStar

typeCheck :: Int -> Context -> TermCheck -> Value -> Result ()
typeCheck i g (Inf e) t =
  do
    t' <- typeInfer i g e
    if quote0 t == quote0 t'
      then return ()
      else
        failure
          ( "Checking type of `"
              ++ show e
              ++ "`, but it's inferred type `"
              ++ show t'
              ++ "` does not match the checked type `"
              ++ show t
              ++ "`. Context: `"
              ++ show g
              ++ "`"
          )
typeCheck i g (Lam e) (VPi t t') = typeCheck (i + 1) ((Local i, t) : g) (substCheck0 (Free (Local i)) e) (t' (vfree (Local i)))
typeCheck i g e t = failure ("Checking type of `" ++ show e ++ "`, but it's not the type `" ++ show t ++ "`. Context: `" ++ show g ++ "`")

substInfer :: Int -> TermInfer -> TermInfer -> TermInfer
substInfer i r (Ann e t) = Ann (substCheck i r e) t
substInfer i r (Bound j) = if i == j then r else Bound j
substInfer i r (Free x) = Free x
substInfer i r (e :@: e') = substInfer i r e :@: substCheck i r e'
substInfer i r Star = Star
substInfer i r (Pi t t') = Pi (substCheck i r t) (substCheck (i + 1) r t')

substCheck0 :: TermInfer -> TermCheck -> TermCheck
substCheck0 = substCheck 0

substCheck :: Int -> TermInfer -> TermCheck -> TermCheck
substCheck i r (Inf e) = Inf (substInfer i r e)
substCheck i r (Lam e) = Lam (substCheck (i + 1) r e)