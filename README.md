# MLTT-and-CT

Church's thesis ($\mathsf{CT}$) states that every function of type $\mathbb{N} \to \mathbb{N}$ is computable in a (Turing-complete) model of computation. The concrete model does not matter, to state $\mathsf{CT}$ and discuss consequences it suffices to work up to a relation $f \sim c$ where $f : \mathbb{N} \to \mathbb{N}$ and $c : \mathbb{N}$ saying that the code $c$ computes the function $f$. Necessarily, this relation is extensional, i.e. if $\forall x.\;f x = g x$ then $f \sim c \leftrightarrow g \sim c$.
