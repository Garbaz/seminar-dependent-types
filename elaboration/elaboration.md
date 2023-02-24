# The Problem with "Type in Type" and a resolution thereof

## Abstract

In "A Tutorial Implementation of a Dependently Typed Lambda Calculus" (A. Löh et al., 2010) a simple dependently typed lambda calculus and a straightforward implementation of type inference and checking for it are presented. In keeping the type rules and implementation simple, they made the deliberate choice to include the rule "type in type", which is commonly known to be inconsistent. Here, this inconsistency will be explored and an extension to the type rules and it's implementation will be presented which resolve it.

## Overview

The type system for which A. Löh et al. [Löh 2010] presented their straightforward implementation in Haskell, which we shall call $\lambda_{\Pi}^{\tau \tau}$ and which will be taken as the basis of the following discussion, is a direct extension of the simply typed lambda calculus (STLC), with function types, $\tau \rightarrow \tau'$, extended to dependent function types, $\forall x : \rho . \rho'$, and the distinction between ordinary terms and type terms being dissolved. From this results the necessity for a term which is the type of all types, $\ast$, which in turn of course also requires a type itself. The perhaps most straightforward choice to be made here is to consider the type of $\ast$ to be $\ast$ itself ("type in type"). Just like in Martin-Löf's 1971 "A Theory of Types" [Martin-Löf 1971] this is in fact the choice that A. Löh et al. made. However, contrary to Martin-Löf in 1971, they did so in full knowledge that this results in an inconsistent type system, as was shown by Girard in 1972 [Girard 1972], to keep the type system and it's implementation simple.

The inconsistency arising from $\ast : \ast$ will be the focus of the first part of this paper. However, instead of Girard's original proof, a much simplified construction due to Hurkens [Hurkens 1995] will be discussed, which in the following shall be called "Hurkens' paradox". From this paradox we will arrive at (relatively) compact concrete term of type $\forall A: \ast. A$, which should be impossible in a consistent type system, given that by applying this term to any possible type we receive a term of that type, including any definitionally empty types. So, looked at through the Curry-Howard Correspondence, where we take types to represent propositions and terms to represent proofs, this entails that we can provide a proof for every possible proposition, which clearly would make such an implementation of little use as the basis for a proof assistant.

While there are different ways of resolving the inconsistency arrising from $\ast : \ast$, in the second part of this paper, one possible solution, namely a "hierarchy of sorts" [Coquand 1986] will be introduced, and an extended version of the lambda calculus and typing implementation presented by A. Löh et al., which we shall call $\lambda_{\Pi}^{\omega}$, will be presented.

For a complete and annotated Agda source file implementing Hurkens' paradox, a translation thereof into the abstract syntax of an implementation of $\lambda_{\Pi}^{\tau \tau}$ in Haskell, and the implementation of $\lambda_{\Pi}^{\omega}$, refer to the code repository associated with this paper [?].

## Hurkens' Paradox

In 1995, Antonius J.C. Hurkens derived, based upon work by Girard [Girard 1972] and Coquand [Coquand 1991], a relatively compact term of type $\bot$ in $\lambda U^-$ [Hurkens 1995]. While the type system of $\lambda U^-$ goes beyond the type system of $\lambda_{\Pi}^{\tau \tau}$, his construction can be followed one-to-one, giving us a term of type $\bot$ in $\lambda_{\Pi}^{\tau \tau}$, proving the type system's inconsistency, which we shall do in the following.

Though Hurkens showed two different approaches to simplifying Girard's paradox, the one for which he provided a complete term of type $\bot$ is based upon the concept of "powerful universes", and will be the one explored here.

While the goal in the end will be to implement the paradox in the mentioned implementation of $\lambda_{\Pi}^{\tau \tau}$, for readability and convenience, in the following, the syntax of the dependently typed programming language Agda [?] will be used in the explanation of the paradox.

In the following, each type theoretic proof, given in Agda syntax, will be accompanied with a corresponding elaborated set theoretic proof which shall aid in understanding of the proof term and it's derivation.

### Basic Definitions

In absence of record types, we will, as is common, define the empty type $\bot$ and negation $\neg$ as follows:

```
⊥ : Set
⊥ = (A : Set) → A

¬ : Set → Set
¬ P = P → ⊥
```

A term of type $\bot$ would have to be a function that could produce a term for any possible type, i.e. a proof of every possible proposition. Therefore this type has to be empty for the type system to be consistent.

A term of type $\neg P$ for some proposition $P$ is simply a function which, if a proof of $P$ were given, would produce a term of type $\bot$. Therefore, if we can construct a term of type $\neg P$, then this means we can not possibly produce a term of type $P$, meaning that the proposition P must not be true. At least that is the case in a consistent type system.

This gives us the first hint as to how we could derive a term of type $\bot$. If we can come up with some proposition $P$ for which we can both derive a term of type $P$ and of type $\neg P$, then we simply have to apply $\neg P$ to $P$ and we will have our term of type $\bot$ in hand. In fact, this will be exactly what we shall do in the end, however, first we have to come up with such a proposition.

For ease of readability and conceptual understanding, we shall also define a function for the type of all propositions over some type $A$. From a set-theoretic perspective, this is to be understood as the set of all subsets for some set $A$, i.e. it's powerset:

```
℘ : Set → Set
℘ A = A → Set
```

This powerset function will be made extensive use of in the following to allow us to build up our paradox.

### A Powerful Universe

The first significant definition for Hurkens' Paradox is an instance of a _powerful universe_, which we shall consider essentially plucked out of thin air, in the knowledge that it will allow us to derive our contradiction:

```
U : Set
U = (A : Set) → (℘ (℘ A) → A) → ℘ (℘ A)

τ : ℘ (℘ U) → U
τ ppU A ppA→A pA = ppU (λ u → pA (ppA→A (u A ppA→A)))

σ : U → ℘ (℘ U)
σ u = u U τ
```

This triple of $(U,\sigma,\tau)$ we consider to be _powerful_, since it satsifies, in set theoretic terms, the following property:

$$
\forall C \in \wp (\wp U): \sigma (\tau C) = \left \{ X | \left \{ y | \tau (\sigma y) \in X \right \} \in C \right \}
$$

We will not concern ourselves with translating this property into type theory or proving that this property holds for our $(U, \sigma, \tau)$ (see Hurkens' original derivation [Hurkens 1995] for some elaboration on the definition of a powerful universe), since such a proof term will not be necessary in constructing our paradox. Rather we will implicitly use this property as it arises from the behaviour of $\tau$ and $\sigma$ as defined above.

### _Inductive_ Subsets and _Well Founded_ Elements

For subsets of $U$ we define the following proposition:

```
inductive' : ℘ (℘ U)
inductive' pU = ((u : U) → σ u pU → pU u)
```

In set theoretic terms this means that for some subset $pU$ of $U$, we consider $pU$ to be _inductive_ iff the following property holds:

$$
\forall u \in U: \left ( pU \in \sigma u \Rightarrow u \in pU \right )
$$

Using this property over subsets of $U$, we define a proposition over elements of $U$:

```
well-founded : ℘ U
well-founded u = (pU : ℘ U) → inductive' pU → pU u
```

In set theoretic terms this means that we consider some element $u$ of $U$ to be _well founded_ iff it is in every inductive subset of $U$.

### A Paradoxical Element 

With $\tau$ from our definition of $U$ as a powerful universe, we pick out a specific element in $U$ for which we can show that it simultaneously is well founded, and isn't well founded, which will give us the contradiction we seek:

```
Ω : U
Ω = τ inductive'
```

This means that in set theoretic terms, we consider $\Omega$ to be $\tau \left \{ pU \in \wp U | pU \, is \, inductive \right \}$.

### The Paradoxical Element is well founded

The proof that $\Omega$ is well founded is relatively straightforward:

```
well-founded-Ω : well-founded Ω
well-founded-Ω pU ind-pU = ind-pU Ω (λ u → ind-pU (τ (σ u)))
```

In set theoretic terms, we need to show that for any inductive subset $pU$ of $U$, $\Omega$ is in $pU$. Knowing that $pU$ is inductive, this means that we need to show that $pU$ is in $\sigma \Omega$.

Since $U$ is powerful, $\sigma \Omega = \left \{ pU \in \wp U | \left \{ u \in U | \tau (\sigma u) \in pU \right \} \, is \, inductive \right \}$. So to show that our $pU$ is in $\sigma \Omega$, we need to show that $\left \{ u \in U | \tau (\sigma u) \in pU \right \}$ is inductive.

Since $pU$ is inductive, we known that for any $u \in U$, if $pU$ is in $\sigma (\tau (\sigma u))$, then $\tau (\sigma u)$ is in $pU$. But this already is exactly what we need to show to prove that $\left \{ u \in U | \tau (\sigma u) \in pU \right \}$ is inductive, therefore our proof is complete.

### But also not well founded

To construct the proof that $\Omega$ is at the same time not well founded, we define one more concept:

```
_<_ : U → U → Set
v < u = (pU : ℘ U) → σ u pU → pU v
```

For some $u \in U$, we consider some $v \in U$ to be a _predecessor_ of $u$ iff for every subset $pU$ of $U$, $pU$ being in $\sigma u$ implies that $v$ is in $pU$.

With this concept, we define ourselves one specific subset of $U$, which will turn out to be inductive:

```
Δ : ℘ U
Δ u = ¬ (τ (σ u) < u)
```

So in set theoretic terms, $\Delta = \left \{ u \in U | \tau (\sigma u) \nless u \right \}$.

We prove that $\Delta$ is inductive:

```
inductive-Δ : inductive' Δ
inductive-Δ u σuΔ τσu<u = τσu<u Δ σuΔ (λ pU → τσu<u λ w → pU (τ (σ w)))
```

To show that $\Delta$ is inductive, we need to show that for any $u \in U$, if $\Delta$ is in $\sigma u$ then $u$ is in $\Delta$, so $\tau (\sigma u) \nless u$.

So for any $u \in U$ with $\Delta \in \sigma u$, we assume $\tau (\sigma u) < u$ and arrive at a contradiction from this assumption as follows:

$\tau (\sigma u) < u$ means that for any $pU$ in $\sigma u$, $\tau (\sigma u)$ is in $pU$. If we take for $pU$ $\Delta$ itself, this means that $\tau (\sigma u)$ is in $\Delta$, so $\tau (\sigma (\tau (\sigma u))) \nless \tau (\sigma u)$.

On the other hand we can show that $\tau (\sigma (\tau (\sigma u))) < \tau (\sigma u)$ as follows:

For any subset $pU$ of $U$ we have to show that if $pU$ is in $\sigma (\tau (\sigma u))$, then $\tau (\sigma (\tau (\sigma u)))$ is in $pU$. However, since $U$ is powerful, this simplifies to having to show that if $\left \{w | \tau (\sigma w) \in pU \right \}$ is in $\sigma u$, then $\tau (\sigma u)$ is in $\left \{w | \tau (\sigma w) \in pU \right \}$. But that follows directly from our initial assumption that $\tau (\sigma u) < u$. Therefore our proof is complete.

With $\Delta$ and the knowledge that it is inductive in hand, we can at last prove that $\Omega$ is not well founded, which will complete the contradiction we seek:

```
¬well-founded-Ω : ¬ (well-founded Ω)
¬well-founded-Ω wfΩ = wfΩ Δ inductive-Δ (λ pU → wfΩ (λ w → pU (τ (σ w))))
```

To show that $\Omega$ is not well founded, we assume that it is, and will from this derive a contradiction:

Since $\Delta$ is inductive and $\Omega$ well founded, this means that $\Omega$ is in $\Delta$, and therefore $\tau (\sigma \Omega) \nless \Omega$. On the other hand, we can show that $\tau (\sigma \Omega) < \Omega$ as follows:

For any subset $pU$ of $U$ we have to show that if $pU$ is in $\sigma \Omega$, then $\tau (\sigma \Omega)$ is in $pU$. However, since $U$ is powerful and $\Omega$ was defined as $\tau \left \{ pU \in \wp U | pU \, is \, inductive \right \}$, this simplifies to having to show that if $\left \{w | \tau (\sigma w) \in pU \right \}$ is inductive, then $\Omega$ is in $\left \{w | \tau (\sigma w) \in pU \right \}$. But that follows directly from our initial assumption that $\Omega$ is well founded. Therefore our proof is complete.

### A term of the empty type

With both a proof that $\Omega$ is well founded and a proof that $\Omega$ is not well founded in hand, we can at last construct the term of type $\bot$:

```
false : ⊥
false = ¬well-founded-Ω well-founded-Ω
```

This concludes the proof that $\lambda_\Pi^{\tau \tau}$ is inconsistent.


## A Hierarchy of Sorts

As evident from the construction of a contradiction in $\lambda_\Pi^{\tau \tau}$ presented above, it is necessary for the expressiveness of our dependently typed lambda calculus to be weakened in some way for it to be consistent. However, we simultaneously do not want to give up the ability to express propositions of practical interest and their proofs in our lambda calculus.

Luckily, a rather simple modification to the type system of $\lambda_\Pi^{\tau \tau}$ is sufficient to make it consistent again [Martin-Löf 1973][Coquand 1986], replacing the problematic type rule $\ast : \ast$ by a _hierarchy of sorts_:

$$
\begin{aligned}
\ast   & : \ast_1\\
\ast_1 & : \ast_2\\
\ast_2 & : \ast_3\\
\ast_3 & : \ast_4\\
& ...
\end{aligned}
$$

So just like in $\lambda_\Pi^{\tau \tau}$ every object term, like $true$, has some type, like $Bool$, and every type term has the kind $\ast$. However, the term $\ast$ itself does not have the kind $\ast$, but the _sort_ $\ast_1$, the term $\ast_1$ has the sort $\ast_2$, the term $\ast_2$ has the sort $\ast_3$ and so on.

In the following, we will use for consistency instead of $\ast$ as the sort of types $\ast_0$.

This lambda calculus we shall call $\lambda_\Pi^\omega$. The grammar and type rules for it are as follows:

$$
\begin{aligned}
e , \rho ::= & \quad e : \rho\\
           | & \quad x\\
           | & \quad e \; e'\\
           | & \quad \lambda x . e\\
           | & \quad \ast_\ell\\
           | & \quad \forall x : \rho . \rho'
\end{aligned}
$$

$$
\frac{\Gamma \vdash e :_\uparrow \tau}
     {\Gamma \vdash e :_\downarrow \tau}
$$

$$
\frac{\Gamma(x) =  \tau}
     {\Gamma \vdash x :_\uparrow \tau}
$$

$$
\frac{\Gamma , x : \tau \vdash e :_\downarrow \tau'}
     {\Gamma \vdash \lambda x . e :_\downarrow \forall x : \tau . \tau'}
$$

$$
\frac{\Gamma \vdash e :_\uparrow \forall x : \tau . \tau' \quad \Gamma \vdash e' :_\downarrow \tau}
     {\Gamma \vdash e \; e' :_\uparrow \tau' \! \left [ \, x \mapsto e' \, \right ]}
$$

$$
\frac{\Gamma \vdash \rho :_\uparrow \ast_\ell \quad \rho \Downarrow \tau \quad \Gamma \vdash e :_\uparrow \tau}
     {\Gamma \vdash (\,e : \rho\,) :_\uparrow \tau}
$$

$$
\frac{\Gamma \vdash \rho :_\uparrow \ast_\ell \quad \rho \Downarrow \tau \quad \Gamma , x : \tau \vdash \rho' :_\uparrow \ast_{\ell'}}
     {\Gamma \vdash \forall x : \rho . \rho' :_\uparrow \ast_{max(\ell, \ell')}}
$$

$$
\frac{}
     {\Gamma \vdash \ast_\ell :_\uparrow \ast_{\ell + 1}}
$$

Only the last three rules differ from $\lambda_\Pi^{\tau \tau}$, and only the last two do so substantially. Also of note is that some type judgements have turned from type checking to type inference due to the need to know the _level_ $\ell$ for a sort $\ast_\ell$, which will in turn necessicate corresponding adaptations in the implementation.

The last type rule, $\ast_\ell : \ast_{\ell + 1}$, is a direct implementation of the hierarchy of sorts as explained above.

However of course it is also necessary to reconsider type judgements over terms $\forall x : \rho . \rho'$ in the second to last type rule. 

One option in defining the type rule for $\forall x : \rho . \rho'$ would be to simply directly keep the rule from $\lambda_\Pi^{\tau \tau}$ in our new type system:

$$
\frac{\Gamma \vdash \rho :_\downarrow \ast_0 \quad \rho \Downarrow \tau \quad \Gamma , x : \tau \vdash \rho' :_\downarrow \ast_0}
     {\Gamma \vdash \forall x : \rho . \rho' :_\uparrow \ast_0}
$$

While this would be consistent (since it is simply a strictly less powerful type system than that of $\lambda_\Pi^\omega$), and would have the advantage of that we would only have to check that the kind of $\rho$ and $\rho'$ is $\ast_0$, it would greatly restrict the expressiveness of our language, since it would mean that a function could not take a type as an argument or return a type as it's result, it could only go from objects to objects.

Instead we will allow for functions to go from any sort to any sort, from objects to types, from types to objects, from kinds to objects, from objects to kinds, etc. :

$$
\frac{\Gamma \vdash \rho :_\uparrow \ast_\ell \quad \rho \Downarrow \tau \quad \Gamma , x : \tau \vdash \rho' :_\uparrow \ast_{\ell'}}
     {\Gamma \vdash \forall x : \rho . \rho' :_\uparrow \ast_{max(\ell, \ell')}}
$$

So the sort of some term $\forall x : \rho . \rho'$ is simply the higher of the sorts of $\rho$ and $\rho'$.

Taking $\rho \rightarrow \rho'$ as a shorthand for $\forall x:\rho . \rho'$ with $x$ not apeparing in $\rho'$, this means for example that a term $\ast_7 \rightarrow \ast_3$ is of the sort $\ast_8$, since $\ast_7 : \ast_8$ and $\ast_3 : \ast_4$.

As a more practical example, the "powerset" function $\wp$ we defined above for our construction of Hurkens' paradox, $\wp A := A \rightarrow \ast_0$, would have the sort $\ast_0 \rightarrow \ast_1$.

This might already hint towards how the construction of Hurkens' paradox presented above will no longer work in $\lambda_\Pi^\omega$, given that it heavily relies on the fact that in $\lambda_{\Pi}^{\tau \tau}$, $\wp : \ast \rightarrow \ast$.

However, the definition of the function $\wp$ above might also raise the question what to do if we do not want to look at the type of all propositions over some type, but rather over some kind, or over some higher sort. Do we define $\wp_1 K := K \rightarrow \ast_0$ of sort $\ast_1 \rightarrow \ast_2$, $\wp_2 S := S \rightarrow \ast_0$ of sort $\ast_2 \rightarrow \ast_3$, and so on?

In the type system presented here, we do not have any other choice but to go the above route. However, there are possible extensions to alleviate this redundancy of definitions, namely _universe polymorphism_ [Sozeau et al. 2014]. However not only does this require levels to become terms inside the lambda calculus itself, but also brings with it the need to introduce a second hierarchy of sorts for level polymorphic function types. We will not implement this here.

## Implementation

With the introduction of hierarchy of sorts having necessitated that some judgements in our type rules have turned from type checking to type inference, the implementation of $\lambda_\Pi^{\tau \tau}$ has to be changed in quite a few places. However, most of these changes are not terribly significant. Rather, we will focus here on the changes to the implementation due to the new type rules for $\,e : \rho\,$, $\forall x : \rho . \rho'$, and $\ast_\ell$.

### The Abstract Syntax Tree Data Type

```hs
data TermInfer
  = Ann TermCheck TermInfer
  | Star Int
  | Pi TermInfer TermInfer
  | Bound Int
  | Free Name
  | TermInfer :@: TermCheck
  deriving (Show, Eq)
```

`Star` now no longer simply is a constant constructor, but has an argument, it's level. And both `Ann` and `Pi` now have in places a `TermCheck` replaced with `TermInfer` due to the necessary changes to the type rules.

### typeInfer for Ann

```hs
typeInfer i g (Ann e r) =
  do
    s <- typeInfer i g r
    case s of
      (VStar l) -> do
        let t = evalInfer [] r
        typeCheck i g e t
        return t
      _ -> failure ":("
```

We infer the type of `r`, which has to be some `VStar l` or we fail. Otherwise we proceed as in the implementation of $\lambda_\Pi^{\tau \tau}$, evaluating `r` to `t` and checking `e` against `t`.

### typeInfer for Pi

```hs
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
          _ -> failure ":("
      _ -> failure ":("
```

We infer the type for `r`, which has to be some `VStar l` or we fail. Otherwise, we evaluate `r` to `t` and infer the type of `r'` in the extended context, which again has to be some `VStar l'`. With both the sort level `l` of `r` and `l'` of `r'` determined, we can return the sort of our `Pi` term, `VStar (max l l')`.

And that is all.