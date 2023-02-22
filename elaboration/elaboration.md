# The Problem with "Type in Type" and it's resolution

## Abstract

## Overview

## Hurkens' Paradox

In 1995, Antonius J.C. Hurkens derived, based upon work by Girard [?] and Coquand [?], a relatively compact term of type $\bot$ in $\lambda U^-$ [?]. While the type system of $\lambda U^-$ goes beyond $\lambda^{\tau \tau}$ ($\lambda_\Pi$ with "Type in Type" [?]), his construction can be followed one-to-one in $\lambda^{\tau \tau}$, which we shall do in the following.

Though Hurkens showed a few different possible simplifications of Girard's paradox, the one for which he provided a complete term of type $\bot$ was based upon the concept of "powerful universes" (elaborated below), and will be the one to be explored here.

While the goal in the end will be to implement the paradox in the mentioned tutorial implementation of $\lambda_\Pi$ with "Type in Type", for readability and convenience, in the following, Agda will be used in the explanation of the paradox, restrained to the use of type features available in our implementation, and with the option `--type-in-type` activated to allow for the paradoxical construction. For a complete annotated Agda file implementing Hurkens' paradox, see the project repository [?].

In absence of record types, we will, as is common, define the empty type $\bot$ and negation $\neg$ as follows:

```
⊥ : Set
⊥ = (A : Set) → A

¬ : Set → Set
¬ P = P → ⊥
```

A term of type $\bot$ would have to be a function that could produce a term for any possible type, i.e. a proof of every possible predicate. Therefore this type has to be empty for the type system to be consistent.

A term of type $\neg P$ for some predicate $P$ is simply a function which, if a proof of $P$ were given, would produce a term of type $\bot$. Therefore, if we can construct a term of type $\neg P$, then this means we can not possibly produce a term of type $P$, meaning that the predicate P is not true. At least that is the case in a consistent type system.

This gives us the first hint as to how we could derive a term of type $\bot$. If we can come up with some predicate $P$ for which we can both derive a term of type $P$ and of type $\neg P$, then we simply have to apply $\neg P$ to $P$ and we will have our term of type $\bot$ in hand. In fact, this will be exactly what we will do in the end, however, first we have to come up with such a predicate.

For ease of readability and conceptual understanding, we will first define a function for the set of all predicates over some type A, which from the perspective of set theory is analogous to the set of all subsets of some set A, i.e. it's powerset:

```
℘ : Set → Set
℘ A = A → Set
```

This powerset function will be made extensive use of in the following to allow us to build up our paradox.

With standard definitions and convenient notation out of the way, we can come to the first significant definition in Hurkens' Paradox, an instance of a _powerful universe_:

```
U : Set
U = (A : Set) → (℘ (℘ A) → A) → ℘ (℘ A)
```

For this universe to be considered "powerful", two functions need to be defined over it:

```
τ : ℘ (℘ U) → U
τ ppU A ppA→A pA = ppU (λ u → pA (ppA→A (u A ppA→A)))

σ : U → ℘ (℘ U)
σ u = u U τ
```

