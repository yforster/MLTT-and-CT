# MLTT-and-CT

Church's thesis ($\mathsf{CT}$) states that every function of type $\mathbb{N} \to \mathbb{N}$ is computable in a (Turing-complete) model of computation. The concrete model does not matter, to state $\mathsf{CT}$ and discuss consequences it suffices to work up to a relation $c \sim f$ where $f : \mathbb{N} \to \mathbb{N}$ and $c : \mathbb{N}$ saying that the code $c$ computes the function $f$. Necessarily, this relation is extensional, i.e. if $\forall x.\;f x = g x$ then $c \sim f \leftrightarrow c \sim g$.

The crucial consequence of $\mathsf{CT}$ is that it allows identifying functions of the type theory with computable functions. Thus, the usual definition of decidability of a predicate $\mathbb{N} \to \mathbb{P}$ (a set in set-theoretic foundations) can be equivalently given in terms of a model of computation, or simply as 

$\mathcal{D} p := \exists f : \mathbb{N} \to \mathbb{B}. \forall x. p x \leftrightarrow f x = \mathsf{true}$

Similarly, we can define enumerability of predicates as

$\mathcal{E} p := \exists f : \mathbb{N} \to \mathbb{N}. \forall x. p x \leftrightarrow \exists n. f n = x + 1$.

Since the halting problem of the underlying model of computation is enumerable and undecidable and furthermore its complement is undecidable, we have that

$\mathsf{CT} \to \exists H : \mathbb{N} \to \mathbb{P}. \mathcal{E} H \land \neg \mathcal{D} H \land \neg \mathcal{D}(\overline H)$.

This allows proving that certain other problems are undecidable, e.g.

$\mathcal{K} (f : \mathbb{N} \to \mathbb{N}) := \exists n. f n > 0$

and its complement.

**Lemma**: If $q$ is decidable and $p$ many-one reduces to $q$ ( $\exists f. \forall x. p x \leftrightarrow q (f x)$ ), then $p$ is decidable.

**Lemma**: $\mathcal{E}(p)$ if and only if $p$ many-one reduces to $\mathcal{K}$

**Lemma**: If $p$ is decidable then $\overline p$ is decidable.

**Corrollary**: $\neg \mathcal{D}(\overline{\mathcal{K}})$
**Proof**: The complement of the halting problem ( $\overline{\mathcal{H}}$ ) is enumerable but undecidable.

We can now turn to $\mathsf{CT}_\Sigma$, the natural formulation of $\mathsf{CT}$ in MLTT:

$\mathsf{CT}_\Sigma := \forall f : \mathbb{N} \to \mathbb{N}.\Sigma c : \mathbb{N}. f \sim c$.

In particular, the $\forall \Sigma$-formulation gives rise to a higher-order coding function:

**Lemma** $\mathsf{CT}_\Sigma \to \exists C: (\mathbb{N} \to \mathbb{N}) \to \mathbb{N}.\forall f. C f \sim f$.

Furthermore, functional extensionality would imply that such a coding function treats its inputs extensionally. However, such an extensional coding function implies that $\overline{\mathcal{K}}$ is decidable, a contradiction to the results before that $\mathsf{CT}_\Sigma$ implies.

**Lemma** Let $C: (\mathbb{N} \to \mathbb{N}) \to \mathbb{N}$ such that $C f \sim f$ for all $f$ and such that $C f = C g$ if $\forall x. f x = g x$. Then $\mathcal{D}(\overline{\mathcal{K}})$.
**Proof**: We need to write a function $F : (\mathbb{N} \to \mathbb{N}) \to \mathbb{B}$ such that $\forall f. F f = \mathsf{true} \leftrightarrow \forall x. f x = 0$. Because $C$ is extensional, we can define $F f := \textbf{if } C f = C (\lambda x.0) \textbf{ then } \mathsf{true} \textbf { else } \mathsf{false}$.

In short: Funect+CT in MLTT implies that the problem of determining whether $\forall x : \mathbb{N}.f n = 0$ is decidable and undecidable.



