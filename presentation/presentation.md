---
marp: true
theme: dracula

math: mathjax

headingDivider: 2

paginate: true
header: An Implementation of Type Checking for a Dependently Typed Lambda Calculus
footer: Tobias Hoffmann

title: An Implementation of Type Checking for a Dependently Typed Lambda Calculus
author: Tobias Hoffmann
---

<style>
section {
    font-size: 30px;
}
</style>

# An Implementation of Type Checking for a <br> Dependently Typed Lambda Calculus

<style>
.outer {
    /* background:blue; */
    display:flex;
    flex-flow: row wrap;
    width:100%;
    height:90%;
}

.inner {
    /* background:green; */
    width:50%;
    display:flex;
    justify-content: center;
    align-items: center;  
}

.inner2 {
    /* background:red; */
    width: 70%;
}
</style>

<style scoped>
  section {
    /* align-items: stretch; */
    display: flex;
    flex-flow: column nowrap;
    justify-content: center;
  }
</style>

<br>

<span style="font-size: 90%"> **Based on:** </span>
_A tutorial implementation of a dependently typed lambda calculus_\
A. Löh, C. McBride, W. Swierstra


## What even are Dependent Types?

- The normal Function type $\, \tau \rightarrow \tau' \,$ is extended to $\, \forall x : \tau . \tau'$
- Also written $\, (x : \tau) \rightarrow \tau' \,$ or $\, \Pi_{x : \tau} \tau'(x)$
- Return type $\tau'$ can depend _value_ of argument $\, x : \tau$
- Like polymorphism, but for all values, not just types

```hs
-- The `cons` function for Lists and Vectors

cons_monomorphic :: Int -> [Int] -> [Int]

cons_polymorphic :: forall a. a -> [a] -> [a]

cons_dependent :: forall (a :: *) (n :: Int). a -> Vec a n -> Vec a (n + 1)
--^ This sadly is not legal Haskell
```


## What even are Dependent Types _for_?

- General Functional Programming
  - **Idris**
  - Stronger compile time invariants

- Proof Assistant
  - **Agda**, **Coq**, **Lean**
  - Automatically check the correctness of proofs
  - → _Curry–Howard Correspondence_


## Proving things with Dependent Types

```hs
-- Associativity of addition on natural numbers in Agda

data ℕ : Set where
  zero : ℕ
  suc  : ℕ -> ℕ

data _==_ : ℕ -> ℕ -> Set where
  refl : {x : ℕ} -> x == x

_+_ : ℕ -> ℕ -> ℕ
zero    + y = y
(suc x) + y = suc (x + y)

assoc : (x : ℕ) -> (y : ℕ) -> (z : ℕ) -> ((x + y) + z) == (x + (y + z))
assoc x y z = ?
```


## Programming with Dependent Types

```hs
-- Known-length vectors and the functions `append` and `head` on them

data Vec : Set -> ℕ -> Set where
    nil  : {A : Set} -> Vec A zero
    _::_ : {A : Set} -> {n : ℕ} -> (a : A) -> Vec A n -> Vec A (suc n)

append : {A : Set} -> {m : ℕ} -> {n : ℕ} -> Vec A m -> Vec A n -> Vec A (m + n)
append nil      v' = v'
append (x :: v) v' = x :: (append v v')

head : {A : Set} -> {n : ℕ} -> Vec A (suc n) -> A
head (x :: v) = x
```


## Inputs and Outputs in Type Rules

$$
\frac{\Gamma \vdash e : \tau \rightarrow \tau' \quad \Gamma \vdash e' : \tau}
     {\Gamma \vdash e \; e' : \tau'}
$$

- How do we translate this into code? What is _input_? What is _output_?
- → **Type Checking** vs **Type Inference** (vs **Program Synthesis**)

- **⇒** We differentiate between:
  - $\Gamma \vdash e :_\downarrow \tau$ ("Check that $e$ has given type $\tau$, in context $\Gamma$")
  - $\Gamma \vdash e :_\uparrow \tau$ ("Infer for $e$ what type $\tau$ it has, in context $\Gamma$")


## Bindings...

$$
\begin{flalign}
& (\lambda x . \lambda y . x) (\lambda y . y)\\
\rightsquigarrow \; & \lambda y . \lambda y . y \qquad \qquad \quad (.\_ \, .?)
\end{flalign}
$$

- There is no silver bullet solution
- We allow for two styles of bindings (→ _locally nameless_)
  - Local: _de Bruijn indices_
  - Global: String names

- For example:
  - $id = \lambda x . x = \lambda \, 0$
  - $const = \lambda x . \lambda y . x = \lambda \, \lambda \, 1$


## The Implementation

For both STLC and DTLC:

```hs
data TermInfer

data TermCheck

-- [...]

typeInfer :: Int -> Context -> TermInfer -> Result Type

typeCheck :: Int -> Context -> TermCheck -> Type -> Result ()

-- [...]
```

## Abstract syntax STLC

<div class="outer">
<div class="inner">

$$
\begin{flalign}

e ::= & \quad e : \tau\\
| & \quad x\\
| & \quad e \; e'\\
| & \quad \lambda x . e\\[7px]

\tau ::= & \quad \alpha\\
| & \quad \tau \rightarrow \tau'\\[7px]
\end{flalign}
$$

</div>
<div class="inner">

```hs
data TermInfer
  = Ann TermCheck Type
  | Bound Int
  | Free Name
  | TermInfer :@: TermCheck

data TermCheck
  = Inf TermInfer
  | Lam TermCheck

data Type
  = TFree Name
  | Fun Type Type
```

</div>
</div>


## Abstract syntax DTLC

<div class="outer">
<div class="inner">

$$
\begin{flalign}
e , \rho ::= & \quad e : \rho\\
| & \quad x\\
| & \quad e \; e'\\
| & \quad \lambda x . e\\
| & \quad \ast\\
| & \quad \forall x : \rho . \rho'
\end{flalign}
$$

</div>
<div class="inner">

```hs
data TermInfer
  = Ann TermCheck TermCheck
  | Bound Int
  | Free Name
  | TermInfer :@: TermCheck
  | Star
  | Pi TermCheck TermCheck

data TermCheck
  = Inf TermInfer
  | Lam TermCheck
```

</div>
</div>


## Type Checking of Inferrable Term

<div class="outer">
<div class="inner">
<div class="inner2">

$$
\frac{\Gamma \vdash e :_\uparrow \tau}
     {\Gamma \vdash e :_\downarrow \tau}
$$

</div>
</div>
<div class="inner">
<div class="inner2">

```hs
typeCheck i g (Inf e) t = do
  t' <- typeInfer i g e
  if t == t'
    then return ()
    else failure ":("
```

</div>
</div>
</div>


## Type Inference of Free Variables

<div class="outer">
<div class="inner">
<div class="inner2">

$$
\frac{\Gamma(x) =  \tau}
     {\Gamma \vdash x :_\uparrow \tau}
$$

</div>
</div>
<div class="inner">
<div class="inner2">

```hs
typeInfer i g (Free x) =
  case lookup x g of
    Just t -> return t
    Nothing -> failure ":("
```

</div>
</div>
</div>


## Type Checking of Abstraction ($\, \lambda x . e \,$)

<div class="outer">
<div class="inner">
<div class="inner2">

$$
\frac{\Gamma , x : \tau \vdash e :_\downarrow \tau'}
     {\Gamma \vdash \lambda x . e :_\downarrow \tau \rightarrow \tau'}
$$

</div>
</div>
<div class="inner">
<div class="inner2">


```hs
typeCheck i g (Lam e) (Fun t t') = 
  typeCheck (i + 1)
    ((Local i, HasType t) : g)
    (substCheck 0 (Free (Local i)) e)
    t'
```

</div>
</div>
<div class="inner">
<div class="inne2">

$$
\frac{\Gamma , x : \tau \vdash e :_\downarrow \tau'}
     {\Gamma \vdash \lambda x . e :_\downarrow \forall x : \tau . \tau'}
$$

</div>
</div>
<div class="inner">
<div class="inner2">

```hs
typeCheck i g (Lam e) (VPi t t') =
  typeCheck (i + 1)
    ((Local i, t) : g)
    (substCheck 0 (Free (Local i)) e)
    (t' (vfree (Local i)))
```

</div>
</div>
</div>


## Type Inference of Application ($\, e \; e' \,$)

<div class="outer">
<div class="inner">
<div class="inner2">

$$
\frac{\Gamma \vdash e :_\uparrow \tau \rightarrow \tau' \quad \Gamma \vdash e' :_\downarrow \tau}
     {\Gamma \vdash e \; e' :_\uparrow \tau'}
$$

</div>
</div>
<div class="inner">
<div class="inner2">

```hs
typeInfer i g (e :@: e') = do
  s <- typeInfer i g e
  case s of
    Fun t t' -> do
      typeCheck i g e' t
      return t'
    _ -> failure ":("
```

</div>
</div>
<div class="inner">
<div class="inner2">

$$
\frac{\Gamma \vdash e :_\uparrow \forall x : \tau . \tau' \quad \Gamma \vdash e' :_\downarrow \tau}
     {\Gamma \vdash e \; e' :_\uparrow \tau' \! \left [ \, x \mapsto e' \, \right ]}
$$

</div>
</div>
<div class="inner">
<div class="inner2">

```hs
typeInfer i g (e :@: e') = do
  s <- typeInfer i g e
  case s of
    VPi t t' -> do
      typeCheck i g e' t
      return
        (t' (evalCheck [] e'))
    _ -> failure ":("
```

</div>
</div>
</div>


## Type Inference of Annotation ($\, e : \rho \,$)

<div class="outer">
<div class="inner">
<div class="inner2">

$$
\frac{\Gamma \vdash \tau : \ast \quad \Gamma \vdash e :_\downarrow \tau}
     {\Gamma \vdash (\,e : \tau\,) :_\uparrow \tau}
$$

</div>
</div>
<div class="inner">
<div class="inner2">


```hs
typeInfer i g (Ann e t) = do
  kindCheck g t Star
  typeCheck i g e t
  return t
```

</div>
</div>
<div class="inner">
<div class="inner2">

$$
\frac{\Gamma \vdash \rho :_\downarrow \ast \quad \rho \Downarrow \tau \quad \Gamma \vdash e :_\downarrow \tau}
     {\Gamma \vdash (\,e : \rho\,) :_\uparrow \tau}
$$

</div>
</div>
<div class="inner">
<div class="inner2">

```hs
typeInfer i g (Ann e r) = do
  typeCheck i g r VStar
  let t = evalCheck [] r
  typeCheck i g e t
  return t
```

</div>
</div>
</div>


## _Kinding_ of Types ($\, \tau \rightarrow \tau' \,$ and $\, \forall x : \rho . \rho' \,$)

<div class="outer">
<div class="inner">
<div class="inner2">

$$
\frac{\Gamma \vdash \tau : \ast \quad \Gamma \vdash \tau' : \ast}
     {\Gamma \vdash \tau \rightarrow \tau' : \ast}
$$

</div>
</div>
<div class="inner">
<div class="inner2">


```hs
kindCheck g (Fun k k') Star = do
  kindCheck g k Star
  kindCheck g k' Star
```

</div>
</div>
<div class="inner">
<div class="inner2">

$$
\frac{\Gamma \vdash \rho :_\downarrow \ast \quad \rho \Downarrow \tau \quad \Gamma , x : \tau \vdash \rho' :_\downarrow \ast}
     {\Gamma \vdash \forall x : \rho . \rho' :_\uparrow \ast}
$$

</div>
</div>
<div class="inner">
<div class="inner2">

```hs
typeInfer i g (Pi r r') = do
  typeCheck i g r VStar
  let t = evalCheck [] r
  typeCheck (i + 1)
    ((Local i, t) : g)
    (substCheck 0
      (Free (Local i)) r')
    VStar
  return VStar
```

</div>
</div>
</div>


## The Type of the Type of Types

<div class="outer" style="height: 25%;">
<div class="inner">
<div class="inner2">

$$
\frac{}
     {\Gamma \vdash \ast :_\uparrow \ast}
$$

</div>
</div>
<div class="inner">
<div class="inner2">

```hs
typeInfer i g Star =
  return VStar
```

</div>
</div>
</div>

- This is _inconsistent_ (→ _Girard's paradox_)
- **⇒** Idea: Introduce a hierarchy of _sorts_
  - $\ast : \ast_1$
  - $\ast_1 : \ast_2$
  - $\ast_2 : \ast_3$
  - ...


## Conclusion

- Implementing type inference & checking isn't scary
- Dependent types aren't either
- But both have their interesting details
- For a practical language we need:
  - A few more features (⚠Beware of Inconsistency⚠)
  - Lots of sugar 


## Sources & co

**Slides at:** https://github.com/Garbaz/seminar-dependent-types

**[1]** Löh, Andres, Conor McBride, Wouter Swierstra. _"A tutorial implementation of a dependently typed lambda calculus."_ Fundamenta informaticae 102.2 (2010): 177-207.
**[2]** Jana Dunfield, Neel Krishnaswami. _"Bidirectional typing"_ ACM Computing Surveys (CSUR) 54.5 (2021): 1-38.