-- import Control.Monad.Error
import Data.Char
import Data.List
import STLC
-- import System.Console.Readline
import System.IO hiding (print)
import Text.ParserCombinators.Parsec hiding (State, parse)
import qualified Text.ParserCombinators.Parsec as P
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Token
import Text.PrettyPrint.HughesPJ hiding (parens)
import qualified Text.PrettyPrint.HughesPJ as PP
import Prelude hiding (print, (<>))

putstrln x = putStrLn x

simplyTyped =
  makeTokenParser
    ( haskellStyle
        { identStart = letter <|> P.char '_',
          reservedNames = ["let", "assume", "putStrLn"]
        }
    )

parseBindings :: CharParser () ([String], [Info])
parseBindings =
  ( let rec :: [String] -> [Info] -> CharParser () ([String], [Info])
        rec e ts =
          do
            (x, t) <-
              parens
                lambdaPi
                ( do
                    x <- identifier simplyTyped
                    reserved simplyTyped "::"
                    t <- pInfo
                    return (x, t)
                )
            (rec (x : e) (t : ts) <|> return (x : e, t : ts))
     in rec [] []
  )
    <|> do
      x <- identifier simplyTyped
      reserved simplyTyped "::"
      t <- pInfo
      return ([x], [t])
  where
    pInfo = fmap HasType (parseType 0 []) <|> fmap (const (HasKind Star)) (reserved simplyTyped "*")

parseStmt :: [String] -> CharParser () (Stmt TermInfer Info)
parseStmt e =
  do
    reserved simplyTyped "let"
    x <- identifier simplyTyped
    reserved simplyTyped "="
    t <- parseTermInfer 0 e
    return (Let x t)
    <|> do
      reserved simplyTyped "assume"
      (xs, ts) <- parseBindings
      return (Assume (reverse (zip xs ts)))
    <|> do
      reserved simplyTyped "putStrLn"
      x <- stringLiteral simplyTyped
      return (PutStrLn x)
    <|> do
      reserved lambdaPi "out"
      x <- option "" (stringLiteral simplyTyped)
      return (Out x)
    <|> fmap Eval (parseTermInfer 0 e)

parseType :: Int -> [String] -> CharParser () Type
parseType 0 e =
  try
    ( do
        t <- parseType 1 e
        rest t <|> return t
    )
  where
    rest t =
      do
        reserved simplyTyped "->"
        t' <- parseType 0 e
        return (Fun t t')
parseType 1 e =
  do
    x <- identifier simplyTyped
    return (TFree (Global x))
    <|> parens simplyTyped (parseType 0 e)

parseTermInfer :: Int -> [String] -> CharParser () TermInfer
parseTermInfer 0 e =
  try
    ( do
        t <- parseTermInfer 1 e
        return t
    )
parseTermInfer 1 e =
  try
    ( do
        t <- parseTermInfer 2 e
        rest (Inf t) <|> return t
    )
    <|> do
      t <- parens simplyTyped (parseLam e)
      rest t
  where
    rest t =
      do
        reserved simplyTyped "::"
        t' <- parseType 0 e
        return (Ann t t')
parseTermInfer 2 e =
  do
    t <- parseTermInfer 3 e
    ts <- many (parseTermCheck 3 e)
    return (foldl (:@:) t ts)
parseTermInfer 3 e =
  do
    x <- identifier simplyTyped
    case findIndex (== x) e of
      Just n -> return (Bound n)
      Nothing -> return (Free (Global x))
    <|> parens simplyTyped (parseTermInfer 0 e)

parseTermCheck :: Int -> [String] -> CharParser () TermCheck
parseTermCheck 0 e =
  parseLam e
    <|> fmap Inf (parseTermInfer 0 e)
parseTermCheck p e =
  try (parens simplyTyped (parseLam e))
    <|> fmap Inf (parseTermInfer p e)

parseLam :: [String] -> CharParser () TermCheck
parseLam e =
  do
    reservedOp simplyTyped "\\"
    xs <- many1 (identifier simplyTyped)
    reservedOp simplyTyped "->"
    t <- parseTermCheck 0 (reverse xs ++ e)
    --  reserved simplyTyped "."
    return (iterate Lam t !! length xs)

parseIO :: String -> CharParser () a -> String -> IO (Maybe a)
parseIO f p x = case P.parse (whiteSpace simplyTyped >> p >>= \x -> eof >> return x) f x of
  Left e -> putStrLn (show e) >> return Nothing
  Right r -> return (Just r)

tPrint :: Int -> Type -> Doc
tPrint p (TFree (Global s)) = text s
tPrint p (Fun ty ty') = parensIf (p > 0) (sep [tPrint 0 ty <> text " ->", nest 2 (tPrint 0 ty')])

iPrint :: Int -> Int -> TermInfer -> Doc
iPrint p ii (Ann c ty) = parensIf (p > 1) (cPrint 2 ii c <> text " :: " <> tPrint 0 ty)
iPrint p ii (Bound k) = text (vars !! (ii - k - 1))
iPrint p ii (Free (Global s)) = text s
iPrint p ii (i :@: c) = parensIf (p > 2) (sep [iPrint 2 ii i, nest 2 (cPrint 3 ii c)])
iPrint p ii x = text ("[" ++ show x ++ "]")

cPrint :: Int -> Int -> TermCheck -> Doc
cPrint p ii (Inf i) = iPrint p ii i
cPrint p ii (Lam c) = parensIf (p > 0) (text "\\ " <> text (vars !! ii) <> text " -> " <> cPrint 0 (ii + 1) c)

vars :: [String]
vars = [c : n | n <- "" : map show [1 ..], c <- ['x', 'y', 'z'] ++ ['a' .. 'w']]

parensIf :: Bool -> Doc -> Doc
parensIf True = PP.parens
parensIf False = id

print = render . cPrint 0 0

printType = render . tPrint 0

lambdaPi =
  makeTokenParser
    ( haskellStyle
        { identStart = letter <|> P.char '_',
          reservedNames = ["forall", "let", "assume", "putStrLn", "out"]
        }
    )

parseStmt_ :: [String] -> CharParser () (Stmt TermInfer_ TermCheck_)
parseStmt_ e =
  do
    reserved lambdaPi "let"
    x <- identifier lambdaPi
    reserved lambdaPi "="
    t <- parseTermInfer_ 0 e
    return (Let x t)
    <|> do
      reserved lambdaPi "assume"
      (xs, ts) <- parseBindings_ False []
      return (Assume (reverse (zip xs ts)))
    <|> do
      reserved lambdaPi "putStrLn"
      x <- stringLiteral lambdaPi
      return (PutStrLn x)
    <|> do
      reserved lambdaPi "out"
      x <- option "" (stringLiteral lambdaPi)
      return (Out x)
    <|> fmap Eval (parseTermInfer_ 0 e)

parseBindings_ :: Bool -> [String] -> CharParser () ([String], [TermCheck_])
parseBindings_ b e =
  ( let rec :: [String] -> [TermCheck_] -> CharParser () ([String], [TermCheck_])
        rec e ts =
          do
            (x, t) <-
              parens
                lambdaPi
                ( do
                    x <- identifier lambdaPi
                    reserved lambdaPi "::"
                    t <- parseTermCheck_ 0 (if b then e else [])
                    return (x, t)
                )
            (rec (x : e) (t : ts) <|> return (x : e, t : ts))
     in rec e []
  )
    <|> do
      x <- identifier lambdaPi
      reserved lambdaPi "::"
      t <- parseTermCheck_ 0 e
      return (x : e, [t])

parseTermInfer_ :: Int -> [String] -> CharParser () TermInfer_
parseTermInfer_ 0 e =
  do
    reserved lambdaPi "forall"
    (fe, t : ts) <- parseBindings_ True e
    reserved lambdaPi "."
    t' <- parseTermCheck_ 0 fe
    return (foldl (\p t -> Pi_ t (Inf_ p)) (Pi_ t t') ts)
    <|> try
      ( do
          t <- parseTermInfer_ 1 e
          rest (Inf_ t) <|> return t
      )
    <|> do
      t <- parens lambdaPi (parseLam_ e)
      rest t
  where
    rest t =
      do
        reserved lambdaPi "->"
        t' <- parseTermCheck_ 0 ([] : e)
        return (Pi_ t t')
parseTermInfer_ 1 e =
  try
    ( do
        t <- parseTermInfer_ 2 e
        rest (Inf_ t) <|> return t
    )
    <|> do
      t <- parens lambdaPi (parseLam_ e)
      rest t
  where
    rest t =
      do
        reserved lambdaPi "::"
        t' <- parseTermCheck_ 0 e
        return (Ann_ t t')
parseTermInfer_ 2 e =
  do
    t <- parseTermInfer_ 3 e
    ts <- many (parseTermCheck_ 3 e)
    return (foldl (:$:) t ts)
parseTermInfer_ 3 e =
  do
    reserved lambdaPi "*"
    return Star_
    <|> do
      n <- natural lambdaPi
      return (toNat_ n)
    <|> do
      x <- identifier lambdaPi
      case findIndex (== x) e of
        Just n -> return (Bound_ n)
        Nothing -> return (Free_ (Global x))
    <|> parens lambdaPi (parseTermInfer_ 0 e)

parseTermCheck_ :: Int -> [String] -> CharParser () TermCheck_
parseTermCheck_ 0 e =
  parseLam_ e
    <|> fmap Inf_ (parseTermInfer_ 0 e)
parseTermCheck_ p e =
  try (parens lambdaPi (parseLam_ e))
    <|> fmap Inf_ (parseTermInfer_ p e)

parseLam_ :: [String] -> CharParser () TermCheck_
parseLam_ e =
  do
    reservedOp lambdaPi "\\"
    xs <- many1 (identifier lambdaPi)
    reservedOp lambdaPi "->"
    t <- parseTermCheck_ 0 (reverse xs ++ e)
    --  reserved lambdaPi "."
    return (iterate Lam_ t !! length xs)

toNat_ :: Integer -> TermInfer_
toNat_ n = Ann_ (toNat_' n) (Inf_ Nat_)

toNat_' :: Integer -> TermCheck_
toNat_' 0 = Zero_
toNat_' n = Succ_ (toNat_' (n - 1))

iPrint_ :: Int -> Int -> TermInfer_ -> Doc
iPrint_ p ii (Ann_ c ty) = parensIf (p > 1) (cPrint_ 2 ii c <> text " :: " <> cPrint_ 0 ii ty)
iPrint_ p ii Star_ = text "*"
iPrint_ p ii (Pi_ d (Inf_ (Pi_ d' r))) =
  parensIf (p > 0) (nestedForall_ (ii + 2) [(ii + 1, d'), (ii, d)] r)
iPrint_ p ii (Pi_ d r) = parensIf (p > 0) (sep [text "forall " <> text (vars !! ii) <> text " :: " <> cPrint_ 0 ii d <> text " .", cPrint_ 0 (ii + 1) r])
iPrint_ p ii (Bound_ k) = text (vars !! (ii - k - 1))
iPrint_ p ii (Free_ (Global s)) = text s
iPrint_ p ii (i :$: c) = parensIf (p > 2) (sep [iPrint_ 2 ii i, nest 2 (cPrint_ 3 ii c)])
iPrint_ p ii Nat_ = text "Nat"
iPrint_ p ii (NatElim_ m z s n) = iPrint_ p ii (Free_ (Global "natElim") :$: m :$: z :$: s :$: n)
iPrint_ p ii (Vec_ a n) = iPrint_ p ii (Free_ (Global "Vec") :$: a :$: n)
iPrint_ p ii (VecElim_ a m mn mc n xs) =
  iPrint_ p ii (Free_ (Global "vecElim") :$: a :$: m :$: mn :$: mc :$: n :$: xs)
iPrint_ p ii (Eq_ a x y) = iPrint_ p ii (Free_ (Global "Eq") :$: a :$: x :$: y)
iPrint_ p ii (EqElim_ a m mr x y eq) =
  iPrint_ p ii (Free_ (Global "eqElim") :$: a :$: m :$: mr :$: x :$: y :$: eq)
iPrint_ p ii (Fin_ n) = iPrint_ p ii (Free_ (Global "Fin") :$: n)
iPrint_ p ii (FinElim_ m mz ms n f) =
  iPrint_ p ii (Free_ (Global "finElim") :$: m :$: mz :$: ms :$: n :$: f)
iPrint_ p ii x = text ("[" ++ show x ++ "]")

cPrint_ :: Int -> Int -> TermCheck_ -> Doc
cPrint_ p ii (Inf_ i) = iPrint_ p ii i
cPrint_ p ii (Lam_ c) = parensIf (p > 0) (text "\\ " <> text (vars !! ii) <> text " -> " <> cPrint_ 0 (ii + 1) c)
cPrint_ p ii Zero_ = fromNat_ 0 ii Zero_ --  text "Zero"
cPrint_ p ii (Succ_ n) = fromNat_ 0 ii (Succ_ n) --  iPrint_ p ii (Free_ (Global "Succ") :$: n)
cPrint_ p ii (Nil_ a) = iPrint_ p ii (Free_ (Global "Nil") :$: a)
cPrint_ p ii (Cons_ a n x xs) =
  iPrint_ p ii (Free_ (Global "Cons") :$: a :$: n :$: x :$: xs)
cPrint_ p ii (Refl_ a x) = iPrint_ p ii (Free_ (Global "Refl") :$: a :$: x)
cPrint_ p ii (FZero_ n) = iPrint_ p ii (Free_ (Global "FZero") :$: n)
cPrint_ p ii (FSucc_ n f) = iPrint_ p ii (Free_ (Global "FSucc") :$: n :$: f)

fromNat_ :: Int -> Int -> TermCheck_ -> Doc
fromNat_ n ii Zero_ = int n
fromNat_ n ii (Succ_ k) = fromNat_ (n + 1) ii k
fromNat_ n ii t = parensIf True (int n <> text " + " <> cPrint_ 0 ii t)

nestedForall_ :: Int -> [(Int, TermCheck_)] -> TermCheck_ -> Doc
nestedForall_ ii ds (Inf_ (Pi_ d r)) = nestedForall_ (ii + 1) ((ii, d) : ds) r
nestedForall_ ii ds x = sep [text "forall " <> sep [parensIf True (text (vars !! n) <> text " :: " <> cPrint_ 0 n d) | (n, d) <- reverse ds] <> text " .", cPrint_ 0 ii x]

data Stmt i tinf
  = Let String i --  let x = t
  | Assume [(String, tinf)] --  assume x :: t, assume x :: *
  | Eval i
  | PutStrLn String --  lhs2TeX hacking, allow to print "magic" string
  | Out String --  more lhs2TeX hacking, allow to print to files
  deriving (Show)

--  read-eval-print loop
readevalprint :: Interpreter i c v t tinf inf -> State v inf -> IO ()
readevalprint int state@(inter, out, ve, te) =
  let rec int state =
        do
          x <-
            catch
              ( if inter
                  then readline (iprompt int)
                  else fmap Just getLine
              )
              (\_ -> return Nothing)
          case x of
            Nothing -> return ()
            Just "" -> rec int state
            Just x ->
              do
                when inter (addHistory x)
                c <- interpretCommand x
                state' <- handleCommand int state c
                maybe (return ()) (rec int) state'
   in do
        --  welcome
        when inter $
          putStrLn
            ( "Interpreter for " ++ iname int ++ ".\n"
                ++ "Type :? for help."
            )
        --  enter loop
        rec int state

data Command
  = TypeOf String
  | Compile CompileForm
  | Browse
  | Quit
  | Help
  | Noop

data CompileForm
  = CompileInteractive String
  | CompileFile String

data InteractiveCommand = Cmd [String] String (String -> Command) String

type NameEnv v = [(Name, v)]

type Ctx inf = [(Name, inf)]

type State v inf = (Bool, String, NameEnv v, Ctx inf)

commands :: [InteractiveCommand]
commands =
  [ Cmd [":type"] "<expr>" TypeOf "print type of expression",
    Cmd [":browse"] "" (const Browse) "browse names in scope",
    Cmd
      [":load"]
      "<file>"
      (Compile . CompileFile)
      "load program from file",
    Cmd [":quit"] "" (const Quit) "exit interpreter",
    Cmd [":help", ":?"] "" (const Help) "display this list of commands"
  ]

helpTxt :: [InteractiveCommand] -> String
helpTxt cs =
  "List of commands:  Any command may be abbreviated to :c where\n"
    ++ "c is the first character in the full name.\n\n"
    ++ "<expr>                  evaluate expression\n"
    ++ "let <var> = <expr>      define variable\n"
    ++ "assume <var> :: <expr>  assume variable\n\n"
    ++ unlines
      ( map
          ( \(Cmd cs a _ d) ->
              let ct = concat (intersperse ", " (map (++ if null a then "" else " " ++ a) cs))
               in ct ++ replicate ((24 - length ct) `max` 2) ' ' ++ d
          )
          cs
      )

interpretCommand :: String -> IO Command
interpretCommand x =
  if isPrefixOf ":" x
    then do
      let (cmd, t') = break isSpace x
          t = dropWhile isSpace t'
      --  find matching commands
      let matching = filter (\(Cmd cs _ _ _) -> any (isPrefixOf cmd) cs) commands
      case matching of
        [] -> do
          putStrLn ("Unknown command `" ++ cmd ++ "'. Type :? for help.")
          return Noop
        [Cmd _ _ f _] ->
          do return (f t)
        x -> do
          putStrLn ("Ambiguous command, could be " ++ concat (intersperse ", " [head cs | Cmd cs _ _ _ <- matching]) ++ ".")
          return Noop
    else return (Compile (CompileInteractive x))

handleCommand :: Interpreter i c v t tinf inf -> State v inf -> Command -> IO (Maybe (State v inf))
handleCommand int state@(inter, out, ve, te) cmd =
  case cmd of
    Quit -> when (not inter) (putStrLn "!@#$^&*") >> return Nothing
    Noop -> return (Just state)
    Help -> putStr (helpTxt commands) >> return (Just state)
    TypeOf x ->
      do
        x <- parseIO "<interactive>" (iiparse int) x
        t <- maybe (return Nothing) (iinfer int ve te) x
        maybe (return ()) (\u -> putStrLn (render (itprint int u))) t
        return (Just state)
    Browse -> do
      putStr (unlines [s | Global s <- reverse (nub (map fst te))])
      return (Just state)
    Compile c ->
      do
        state <- case c of
          CompileInteractive s -> compilePhrase int state s
          CompileFile f -> compileFile int state f
        return (Just state)

compileFile :: Interpreter i c v t tinf inf -> State v inf -> String -> IO (State v inf)
compileFile int state@(inter, out, ve, te) f =
  do
    x <- readFile f
    stmts <- parseIO f (many (isparse int)) x
    maybe (return state) (foldM (handleStmt int) state) stmts

compilePhrase :: Interpreter i c v t tinf inf -> State v inf -> String -> IO (State v inf)
compilePhrase int state@(inter, out, ve, te) x =
  do
    x <- parseIO "<interactive>" (isparse int) x
    maybe (return state) (handleStmt int state) x

data Interpreter i c v t tinf inf = I
  { iname :: String,
    iprompt :: String,
    iitype :: NameEnv v -> Ctx inf -> i -> Result t,
    iquote :: v -> c,
    ieval :: NameEnv v -> i -> v,
    ihastype :: t -> inf,
    icprint :: c -> Doc,
    itprint :: t -> Doc,
    iiparse :: CharParser () i,
    isparse :: CharParser () (Stmt i tinf),
    iassume :: State v inf -> (String, tinf) -> IO (State v inf)
  }

st :: Interpreter TermInfer TermCheck Value Type Info Info
st =
  I
    { iname = "the simply typed lambda calculus",
      iprompt = "ST> ",
      iitype = \v c -> iType 0 c,
      iquote = quote0,
      ieval = \e x -> iEval x (e, []),
      ihastype = HasType,
      icprint = cPrint 0 0,
      itprint = tPrint 0,
      iiparse = parseTermInfer 0 [],
      isparse = parseStmt [],
      iassume = \s (x, t) -> stassume s x t
    }

lp :: Interpreter TermInfer_ TermCheck_ Value_ Value_ TermCheck_ Value_
lp =
  I
    { iname = "lambda-Pi",
      iprompt = "LP> ",
      iitype = \v c -> iType_ 0 (v, c),
      iquote = quote0_,
      ieval = \e x -> iEval_ x (e, []),
      ihastype = id,
      icprint = cPrint_ 0 0,
      itprint = cPrint_ 0 0 . quote0_,
      iiparse = parseTermInfer_ 0 [],
      isparse = parseStmt_ [],
      iassume = \s (x, t) -> lpassume s x t
    }

lpte :: Ctx Value_
lpte =
  [ (Global "Zero", VNat_),
    (Global "Succ", VPi_ VNat_ (\_ -> VNat_)),
    (Global "Nat", VStar_),
    ( Global "natElim",
      VPi_
        (VPi_ VNat_ (\_ -> VStar_))
        ( \m ->
            VPi_
              (m `vapp_` VZero_)
              ( \_ ->
                  VPi_
                    (VPi_ VNat_ (\k -> VPi_ (m `vapp_` k) (\_ -> (m `vapp_` (VSucc_ k)))))
                    ( \_ ->
                        VPi_ VNat_ (\n -> m `vapp_` n)
                    )
              )
        )
    ),
    (Global "Nil", VPi_ VStar_ (\a -> VVec_ a VZero_)),
    ( Global "Cons",
      VPi_
        VStar_
        ( \a ->
            VPi_
              VNat_
              ( \n ->
                  VPi_ a (\_ -> VPi_ (VVec_ a n) (\_ -> VVec_ a (VSucc_ n)))
              )
        )
    ),
    (Global "Vec", VPi_ VStar_ (\_ -> VPi_ VNat_ (\_ -> VStar_))),
    ( Global "vecElim",
      VPi_
        VStar_
        ( \a ->
            VPi_
              (VPi_ VNat_ (\n -> VPi_ (VVec_ a n) (\_ -> VStar_)))
              ( \m ->
                  VPi_
                    (m `vapp_` VZero_ `vapp_` (VNil_ a))
                    ( \_ ->
                        VPi_
                          ( VPi_
                              VNat_
                              ( \n ->
                                  VPi_
                                    a
                                    ( \x ->
                                        VPi_
                                          (VVec_ a n)
                                          ( \xs ->
                                              VPi_
                                                (m `vapp_` n `vapp_` xs)
                                                ( \_ ->
                                                    m `vapp_` VSucc_ n `vapp_` VCons_ a n x xs
                                                )
                                          )
                                    )
                              )
                          )
                          ( \_ ->
                              VPi_
                                VNat_
                                ( \n ->
                                    VPi_ (VVec_ a n) (\xs -> m `vapp_` n `vapp_` xs)
                                )
                          )
                    )
              )
        )
    ),
    ( Global "Refl",
      VPi_
        VStar_
        ( \a ->
            VPi_
              a
              ( \x ->
                  VEq_ a x x
              )
        )
    ),
    (Global "Eq", VPi_ VStar_ (\a -> VPi_ a (\x -> VPi_ a (\y -> VStar_)))),
    ( Global "eqElim",
      VPi_
        VStar_
        ( \a ->
            VPi_
              (VPi_ a (\x -> VPi_ a (\y -> VPi_ (VEq_ a x y) (\_ -> VStar_))))
              ( \m ->
                  VPi_
                    (VPi_ a (\x -> m `vapp_` x `vapp_` x `vapp_` VRefl_ a x))
                    ( \_ ->
                        VPi_
                          a
                          ( \x ->
                              VPi_
                                a
                                ( \y ->
                                    VPi_
                                      (VEq_ a x y)
                                      ( \eq ->
                                          m `vapp_` x `vapp_` y `vapp_` eq
                                      )
                                )
                          )
                    )
              )
        )
    ),
    (Global "FZero", VPi_ VNat_ (\n -> VFin_ (VSucc_ n))),
    ( Global "FSucc",
      VPi_
        VNat_
        ( \n ->
            VPi_
              (VFin_ n)
              ( \f ->
                  VFin_ (VSucc_ n)
              )
        )
    ),
    (Global "Fin", VPi_ VNat_ (\n -> VStar_)),
    ( Global "finElim",
      VPi_
        (VPi_ VNat_ (\n -> VPi_ (VFin_ n) (\_ -> VStar_)))
        ( \m ->
            VPi_
              (VPi_ VNat_ (\n -> m `vapp_` (VSucc_ n) `vapp_` (VFZero_ n)))
              ( \_ ->
                  VPi_
                    (VPi_ VNat_ (\n -> VPi_ (VFin_ n) (\f -> VPi_ (m `vapp_` n `vapp_` f) (\_ -> m `vapp_` (VSucc_ n) `vapp_` (VFSucc_ n f)))))
                    ( \_ ->
                        VPi_
                          VNat_
                          ( \n ->
                              VPi_
                                (VFin_ n)
                                ( \f ->
                                    m `vapp_` n `vapp_` f
                                )
                          )
                    )
              )
        )
    )
  ]

lpve :: Ctx Value_
lpve =
  [ (Global "Zero", VZero_),
    (Global "Succ", VLam_ (\n -> VSucc_ n)),
    (Global "Nat", VNat_),
    (Global "natElim", cEval_ (Lam_ (Lam_ (Lam_ (Lam_ (Inf_ (NatElim_ (Inf_ (Bound_ 3)) (Inf_ (Bound_ 2)) (Inf_ (Bound_ 1)) (Inf_ (Bound_ 0)))))))) ([], [])),
    (Global "Nil", VLam_ (\a -> VNil_ a)),
    ( Global "Cons",
      VLam_
        ( \a ->
            VLam_
              ( \n ->
                  VLam_
                    ( \x ->
                        VLam_
                          ( \xs ->
                              VCons_ a n x xs
                          )
                    )
              )
        )
    ),
    (Global "Vec", VLam_ (\a -> VLam_ (\n -> VVec_ a n))),
    (Global "vecElim", cEval_ (Lam_ (Lam_ (Lam_ (Lam_ (Lam_ (Lam_ (Inf_ (VecElim_ (Inf_ (Bound_ 5)) (Inf_ (Bound_ 4)) (Inf_ (Bound_ 3)) (Inf_ (Bound_ 2)) (Inf_ (Bound_ 1)) (Inf_ (Bound_ 0)))))))))) ([], [])),
    (Global "Refl", VLam_ (\a -> VLam_ (\x -> VRefl_ a x))),
    (Global "Eq", VLam_ (\a -> VLam_ (\x -> VLam_ (\y -> VEq_ a x y)))),
    (Global "eqElim", cEval_ (Lam_ (Lam_ (Lam_ (Lam_ (Lam_ (Lam_ (Inf_ (EqElim_ (Inf_ (Bound_ 5)) (Inf_ (Bound_ 4)) (Inf_ (Bound_ 3)) (Inf_ (Bound_ 2)) (Inf_ (Bound_ 1)) (Inf_ (Bound_ 0)))))))))) ([], [])),
    (Global "FZero", VLam_ (\n -> VFZero_ n)),
    (Global "FSucc", VLam_ (\n -> VLam_ (\f -> VFSucc_ n f))),
    (Global "Fin", VLam_ (\n -> VFin_ n)),
    (Global "finElim", cEval_ (Lam_ (Lam_ (Lam_ (Lam_ (Lam_ (Inf_ (FinElim_ (Inf_ (Bound_ 4)) (Inf_ (Bound_ 3)) (Inf_ (Bound_ 2)) (Inf_ (Bound_ 1)) (Inf_ (Bound_ 0))))))))) ([], []))
  ]

repLP :: Bool -> IO ()
repLP b = readevalprint lp (b, [], lpve, lpte)

repST :: Bool -> IO ()
repST b = readevalprint st (b, [], [], [])

iinfer int d g t =
  case iitype int d g t of
    Left e -> putStrLn e >> return Nothing
    Right v -> return (Just v)

handleStmt ::
  Interpreter i c v t tinf inf ->
  State v inf ->
  Stmt i tinf ->
  IO (State v inf)
handleStmt int state@(inter, out, ve, te) stmt =
  do
    case stmt of
      Assume ass -> foldM (iassume int) state ass
      Let x e -> checkEval x e
      Eval e -> checkEval it e
      PutStrLn x -> putStrLn x >> return state
      Out f -> return (inter, f, ve, te)
  where
    --  checkEval :: String -> i -> IO (State v inf)
    checkEval i t =
      check
        int
        state
        i
        t
        ( \(y, v) -> do
            --  ugly, but we have limited space in the paper
            --  usually, you'd want to have the bound identifier *and*
            --  the result of evaluation
            let outtext =
                  if i == it
                    then render (icprint int (iquote int v) <> text " :: " <> itprint int y)
                    else render (text i <> text " :: " <> itprint int y)
            putStrLn outtext
            unless (null out) (writeFile out (process outtext))
        )
        (\(y, v) -> (inter, "", (Global i, v) : ve, (Global i, ihastype int y) : te))

check ::
  Interpreter i c v t tinf inf ->
  State v inf ->
  String ->
  i ->
  ((t, v) -> IO ()) ->
  ((t, v) -> State v inf) ->
  IO (State v inf)
check int state@(inter, out, ve, te) i t kp k =
  do
    --  typecheck and evaluate
    x <- iinfer int ve te t
    case x of
      Nothing ->
        do
          --  putStrLn "type error"
          return state
      Just y ->
        do
          let v = ieval int ve t
          kp (y, v)
          return (k (y, v))

stassume state@(inter, out, ve, te) x t = return (inter, out, ve, (Global x, t) : te)

lpassume state@(inter, out, ve, te) x t =
  check
    lp
    state
    x
    (Ann_ t (Inf_ Star_))
    (\(y, v) -> return ()) --  putStrLn (render (text x <> text " :: " <> cPrint_ 0 0 (quote0_ v))))
    (\(y, v) -> (inter, out, ve, (Global x, v) : te))

it = "it"

process :: String -> String
process = unlines . map (\x -> "< " ++ x) . lines

main :: IO ()
main = repLP True