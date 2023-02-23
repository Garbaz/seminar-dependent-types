# The Problem with "Type in Type" and a resolution thereof

## Abstract

In "A Tutorial Implementation of a Dependently Typed Lambda Calculus" (A. Löh et al., 2010) a simple dependently typed lambda calculus and a straightforward implementation of type inference and checking for it are presented. In keeping the type rules and implementation simple, they made the deliberate choice to include the rule "type in type", which is commonly known to be inconsistent. Here, this inconsistency will be explored and an extension to the type rules and it's implementation will be presented which resolve it.

## Overview

The type system for which A. Löh et al. ((Löh 2010)) presented their straightforward implementation in Haskell, which we shall call $\lambda_{\Pi}^{\tau \tau}$ and which will be taken as the basis of the following discussion, is a direct extension of the simply typed lambda calculus (STLC), with function types ($\tau \rightarrow \tau'$) extended to dependent function types ($\forall x : \rho . \rho'$), and the distinction between ordinary terms and type terms being dissolved. From this results the necessity for a term which is the type of all types ($\ast$), which in turn of course also requires a type itself. The perhaps most straightforward choice to be made here is to consider the type of $\ast$ to be $\ast$ itself ("type in type"). Just like in Martin-Löf's 1971 "A Theory of Types" ((Martin-Löf 1971)) this is in fact the choice that A. Löh et al. made. However, contrary to Martin-Löf in 1971, they did so in full knowledge that this results in an inconsistent type system, as was shown by Girard in 1972 ((Girard 1972)).

This inconsistency arising from $\ast : \ast$ will be the focus of the first part of this document. However, instead of Girard's original proof, a much simplified construction due to Hurkens ((Hurkens 1995)) will be discussed, which in the following shall be called "Hurkens' paradox". From this paradox we will arrive at (relatively) compact concrete term of type $\forall A: \ast. A$, which should be impossible in a consistent type system, given that from this we can derive a term for any possible type, including any definitionally empty type. So, through the Curry-Howard Correspondence, taking types to represent predicates and terms to represent proofs, we can provide a proof for every possible predicate, which clearly would make our implementation of little use as the basis for a proof assistant.

While there are different ways of resolving the inconsistency arrising from $\ast : \ast$, in the second part of this document, one possible solution, namely a "hierarchy of sorts" ((Coquand 1986)) will be introduced and an extension of the implementation presented by A. Löh et al. to this once again consistent dependently typed lambda calculus, which we shall call $\lambda_{\Pi}^{\omega}$ will be presented.

## Hurkens' Paradox

In 1995, Antonius J.C. Hurkens derived, based upon work by Girard ((Girard 1972)) and Coquand ((Coquand 1991)), a relatively compact term of type $\bot$ in $\lambda U^-$ ((Hurkens 1995)). While the type system of $\lambda U^-$ goes beyond the type system of $\lambda_{\Pi}^{\tau \tau}$, his construction can be followed one-to-one, giving us a term of type $\bot$ in $\lambda_{\Pi}^{\tau \tau}$, proving the type system's inconsistency, which we shall do in the following.

Though Hurkens showed a few different possible simplifications of Girard's paradox, the one for which he provided a complete term of type $\bot$ was based upon the concept of "powerful universes", and will be the one to be explored here.

While the goal in the end will be to implement the paradox in the mentioned implementation of $\lambda_{\Pi}^{\tau \tau}$, for readability and convenience, in the following, the syntax of the dependently typed programming language Agda ((?)) will be used in the explanation of the paradox, restrained to the use of type features available in our implementation, and with the option `--type-in-type` active.

For a complete annotated Agda source file implementing Hurkens' paradox, the translation thereof into the abstract syntax of our implementation of $\lambda_{\Pi}^{\tau \tau}$ in Haskell, and also the fully expanded term in Haskell, see the code repository associated with this document ((?)).

In absence of record types, we will, as is common, define the empty type $\bot$ and negation $\neg$ as follows:

```
⊥ : Set
⊥ = (A : Set) → A

¬ : Set → Set
¬ P = P → ⊥
```

A term of type $\bot$ would have to be a function that could produce a term for any possible type, i.e. a proof of every possible predicate. Therefore this type has to be empty for the type system to be consistent.

A term of type $\neg P$ for some predicate $P$ is simply a function which, if a proof of $P$ were given, would produce a term of type $\bot$. Therefore, if we can construct a term of type $\neg P$, then this means we can not possibly produce a term of type $P$, meaning that the predicate P must not be true. At least that is the case in a consistent type system.

This gives us the first hint as to how we could derive a term of type $\bot$. If we can come up with some predicate $P$ for which we can both derive a term of type $P$ and of type $\neg P$, then we simply have to apply $\neg P$ to $P$ and we will have our term of type $\bot$ in hand. In fact, this will be exactly what we shall do in the end, however, first we have to come up with such a predicate.

For ease of readability and conceptual understanding, we shall also define a function for the type of all predicates over some type $A$. From a set-theoretic perspective, this is to be understood as the set of all subsets for some set $A$, i.e. it's powerset:

```
℘ : Set → Set
℘ A = A → Set
```

This powerset function will be made extensive use of in the following to allow us to build up our paradox.

With all that preamble sorted, we can come to the first significant definition in Hurkens' Paradox, an instance of a _powerful universe_:

```
U : Set
U = (A : Set) → (℘ (℘ A) → A) → ℘ (℘ A)

τ : ℘ (℘ U) → U
τ ppU A ppA→A pA = ppU (λ u → pA (ppA→A (u A ppA→A)))

σ : U → ℘ (℘ U)
σ u = u U τ
```

For the purpose of our understanding, these definitions can be considered as essentially plucked out of thin air, with the knowledege that it will aid us in constructing our paradox. 

This triple of $(U,\sigma,\tau)$ we consider to be _powerful_, since it satsifies, in set theoretic terms, the following property:

$$
\forall C \in \wp \wp U: \sigma \tau C = \left \{ X | \left \{ y | \tau \sigma y \in X \right \} \in C \right \}
$$

We will not concern ourselves with translating this property into type theory or proving that this property holds for our $(U, \sigma, \tau)$ (see Hurkens' original derivation ((Hurkens 1995)) for some elaboration on the definition of a powerful universe), since such a proof will not be necessary in constructing our paradox.

Rather, we shall define a property over subsets of $U$:

```
inductive' : ℘ (℘ U)
inductive' pU = ((u : U) → σ u pU → pU u)
```

In set theoretic terms this means that for some subset of $U$, $pU$, we consider this subset to be _inductive_ if it has the following property:

$$
\forall u \in U: \left ( pU \in \sigma u \Rightarrow u \in pU \right )
$$

