module EDTLC where

data TermInfer
  = Ann TermCheck TermInfer
  | Star Int
  | Pi TermInfer TermInfer
  | Bound Int
  | Free Name
  | TermInfer :@: TermCheck
  deriving (Show, Eq)

data TermCheck
  = Inf TermInfer
  | Lam TermCheck
  deriving (Show, Eq)

iAnn t t' = Inf (Ann t t')

iStar l = Inf (Star l)

star0 = Star 0

iStar0 = iStar 0

iPi t t' = Inf (Pi t t')

iBound = Inf . Bound

iFree = Inf . Free

data Name
  = Global String
  | Local Int
  | Quote Int
  deriving (Show, Eq)

data Value
  = VLam (Value -> Value)
  | VStar Int
  | VPi Value (Value -> Value)
  | VNeutral Neutral

instance Show Value where
  show v = "(evalInfer [] (" ++ show (quote0 v) ++ "))"

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
evalInfer d (Star l) = VStar l
evalInfer d (Pi t t') = VPi (evalInfer d t) (\x -> evalInfer (x : d) t')

evalCheck :: Env -> TermCheck -> Value
evalCheck d (Inf i) = evalInfer d i
evalCheck d (Lam e) = VLam (\x -> evalCheck (x : d) e)

quote0 :: Value -> TermCheck
quote0 = quoteCheck 0

quoteCheck :: Int -> Value -> TermCheck
quoteCheck i (VLam f) = Lam (quoteCheck (i + 1) (f (vfree (Quote i))))
quoteCheck i (VNeutral n) = Inf (neutralQuote i n)
quoteCheck i (VStar l) = Inf (Star l)
quoteCheck i (VPi v f) = Inf (Pi (quoteInfer i v) (quoteInfer (i + 1) (f (vfree (Quote i)))))

quoteInfer :: Int -> Value -> TermInfer
quoteInfer i (VLam f) = error "We can not quote a lambda value to a TermInfer. Something is terribly wrong!"
quoteInfer i (VNeutral n) = neutralQuote i n
quoteInfer i (VStar l) = Star l
quoteInfer i (VPi v f) = Pi (quoteInfer i v) (quoteInfer (i + 1) (f (vfree (Quote i))))

neutralQuote :: Int -> Neutral -> TermInfer
neutralQuote i (NFree x) = boundfree i x
neutralQuote i (NApp n v) = neutralQuote i n :@: quoteCheck i v

boundfree :: Int -> Name -> TermInfer
boundfree i (Quote k) = Bound (i - k - 1)
boundfree i x = Free x

type Context = [(Name, Value)]

type Result a = Either String a

failure :: String -> Result a
failure = Left

typeInfer0 :: Context -> TermInfer -> Result Value
typeInfer0 = typeInfer 0

typeInfer :: Int -> Context -> TermInfer -> Result Value
typeInfer i g (Ann e r) =
  do
    s <- typeInfer i g r
    case s of
      (VStar l) -> do
        let t = evalInfer [] r
        typeCheck i g e t
        return t
      _ -> failure ("The type of `" ++ show r ++ "` should be `VStar _`, but it is `" ++ show s ++ "`.")
typeInfer i g (Bound j) = failure ("Trying to infer type of bound variable `" ++ show j ++ "`, but we don't do that.")
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
      _ ->
        failure
          ( "Inferring type of `" ++ show e
              ++ "` of type `"
              ++ show s
              ++ "`, applied to `"
              ++ show e'
              ++ "`, but the former isn't a function."
          )
typeInfer i g (Star l) = return (VStar (l + 1))
typeInfer i g (Pi r r') =
  do
    s <- typeInfer i g r
    case s of
      (VStar l) -> do
        let t = evalInfer [] r
        s' <-
          typeInfer
            (i + 1)
            ((Local i, t) : g)
            (substInfer 0 (Free (Local i)) r')
        case s' of
          (VStar l') -> return (VStar (max l l'))
          _ -> failure ("The type of `" ++ show r' ++ "` should be `VStar _`, but it is `" ++ show s' ++ "`.")
      _ -> failure ("The type of `" ++ show r ++ "` should be `VStar _`, but it is `" ++ show s ++ "`.")

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
typeCheck i g (Lam e) (VPi t t') =
  typeCheck
    (i + 1)
    ((Local i, t) : g)
    (substCheck 0 (Free (Local i)) e)
    (t' (vfree (Local i)))
typeCheck i g e t = failure ("Checking type of `" ++ show e ++ "`, but it's not the type `" ++ show t ++ "`. Context: `" ++ show g ++ "`")

substInfer :: Int -> TermInfer -> TermInfer -> TermInfer
substInfer i r (Ann e t) = Ann (substCheck i r e) t
substInfer i r (Bound j) = if i == j then r else Bound j
substInfer i r (Free x) = Free x
substInfer i r (e :@: e') = substInfer i r e :@: substCheck i r e'
substInfer i r (Star l) = Star l
substInfer i r (Pi t t') = Pi (substInfer i r t) (substInfer (i + 1) r t')

substCheck :: Int -> TermInfer -> TermCheck -> TermCheck
substCheck i r (Inf e) = Inf (substInfer i r e)
substCheck i r (Lam e) = Lam (substCheck (i + 1) r e)