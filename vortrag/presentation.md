---
marp: true
theme: dracula

math: mathjax

headingDivider: 2

paginate: true
header: Tutorial Implementation of a Dependently Typed Lambda Calculus
footer: Tobias Hoffmann

title: Tutorial Implementation of a Dependently Typed Lambda Calculus
author: Tobias Hoffmann
---

<style>
section {
    font-size: 30px;
}
</style>

# An Implementation of Type checking for a <br> Dependently Typed Lambda Calculus

<link rel="stylesheet" href="style.css">

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

- The normal Function type $\tau \rightarrow \tau'$ is extended to $(x :: \tau) \rightarrow \tau'$
- Also commonly written as $\forall x :: \tau . \tau'$ or $\Pi_{x :: \tau} \tau'(x)$
- The return type _(range)_ can now depend on the argument type _(domain)_
- Like polymorphism, but for all values, not just types

```hs
-- The `cons` function for lists and vectors

cons_monomorphic :: Int -> List Int -> List Int

cons_polymorphic :: (a :: *) -> List a -> List a

cons_dependent :: (n :: Nat) -> (a :: *) -> Vec a n -> Vec a (1 + n)
```


## Dependent Types in Practice

- General Functional Programming
  - **Idris**
  - Stronger compile time invariants

- Proof Assistant
  - **Agda**, **Coq**
  - Automatically check the correctness of proofs


## Programming with Dependent Types

```hs
-- Known-length vectors and the functions `append` and `head` on them

data Vec : Set -> Nat -> Set where
    nil  : {a : Set} -> Vec a 0
    _::_ : {a : Set} -> {n : Nat} -> a -> Vec a n -> Vec a (1 + n)

append : {a : Set} -> {n m : Nat} -> Vec a n -> Vec a m -> Vec a (n + m)
append nil v' = v'
append (x :: v) v' = x :: (append v v')

head : {a : Set} -> {n : Nat} -> {1 <= n} -> Vec a n -> a
head (x :: v) = x
```


## Proving things with Dependent Types

```hs
-- Associativity of addition on natural numbers in Agda

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

_+_ : Nat -> Nat -> Nat
zero + y = y
(suc x) + y = suc (x + y)

data _==_ (x : Nat) -> Set where
  refl : x == x

assoc : (x : Nat) -> (y : Nat) -> (z : Nat) -> (x + y) + z == x + (y + z)
assoc x y z = ?
```


## Inputs and Outputs in Typing Judgements

...

=> Differentiate between inferrable Terms and checkable Terms

...


## Abstract syntax STLC

<div class="outer">
<div class="inner">

$$
\begin{flalign}

e ::= & \quad e :: \tau\\
| & \quad x\\
| & \quad e \; e'\\
| & \quad \lambda x \rightarrow e\\[7px]

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
e , \rho , \kappa ::= & \quad e :: \rho\\
| & \quad \ast\\
| & \quad \forall x :: \rho . \rho'\\
| & \quad x\\
| & \quad e \; e'\\
| & \quad \lambda x \rightarrow e\\[7px]
\end{flalign}
$$

</div>
<div class="inner">

```hs
data TermInfer
  = Ann TermCheck TermCheck
  | Star
  | Pi TermCheck TermCheck
  | Bound Int
  | Free Name
  | TermInfer :@: TermCheck

data TermCheck
  = Inf TermInfer
  | Lam TermCheck
```

</div>
</div>


## ((Something simple here as intro))

...


## Interlude: Bound Variables 😬

- There is no silver bullet solution
- We use a combintation of two styles of bindings (→ _locally nameless_)
  - Local: _de Bruijn indices_
  - Global: _String names_

- E.g.: $const = \lambda \rightarrow \lambda \rightarrow 1$

## Type Inference of Application ($e \; e'$)

<div class="outer">
<div class="inner">

$$
\frac{\Gamma \vdash e ::_\uparrow \tau \rightarrow \tau' \quad \Gamma \vdash e' ::_\downarrow \tau}
     {\Gamma \vdash e \; e' ::_\uparrow \tau'}
$$

</div>
<div class="inner">

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
<div class="inner">

$$
\frac{\Gamma \vdash e ::_\uparrow \forall x :: \tau . \tau' \quad \Gamma \vdash e' ::_\downarrow \tau}
     {\Gamma \vdash e \; e' ::_\uparrow \tau \! \left [ \, x \mapsto e' \, \right ]}
$$

</div>
<div class="inner">

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


## Type Inference of Annotation ($e :: \rho$)

<div class="outer">
<div class="inner">

$$
\frac{\Gamma \vdash \tau :: \ast \quad \Gamma \vdash e ::_\downarrow \tau}
     {\Gamma \vdash (\,e :: \tau\,) ::_\uparrow \tau}
$$

</div>
<div class="inner">


```hs
typeInfer i g (Ann e t) = do
  kindCheck g t Star
  typeCheck i g e t
  return t
```

</div>
<div class="inner">

$$
\frac{\Gamma \vdash \rho ::_\downarrow \ast \quad \rho \Downarrow \tau \quad \Gamma \vdash e ::_\downarrow \tau}
     {\Gamma \vdash (\,e :: \rho\,) ::_\uparrow \tau}
$$

</div>
<div class="inner">

```hs
typeInfer i g (Ann e r) = do
  typeCheck i g r VStar
  let t = evalCheck [] r
  typeCheck i g e t
  return t
```

</div>
</div>


## Kind Inference of Types ($\tau \rightarrow \tau'$ and $\forall x :: \rho . \rho'$)

...


## Issues & Extensions

...


## Conclusion

- Dependent types aren't as scary as they seem
- ...


## Sources & co

**Slides at:** https://github.com/Garbaz/seminar-dependent-types

**[1]** Löh, Andres, Conor McBride, and Wouter Swierstra. _"A tutorial implementation of a dependently typed lambda calculus."_ Fundamenta informaticae 102.2 (2010): 177-207.