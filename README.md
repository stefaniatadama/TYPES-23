# Revisiting Containers in Cubical Agda

Supplementary artefacts for TYPES 2023. Typechecked using Agda 2.6.3 and Cubical v0.5.

- **Containers.agda**: Definition of generalised containers, the category $\underline{\mathbf{Cont}}$ of generalised containers, and the container extension functor ⟦\_⟧ mapping generalised containers to functors.
- **ContainersProofs.agda**: Two proofs of the central result that the container extension functor ⟦\_⟧ is full and faithful. One follows the proof given in [Containers: Constructing strictly positive types](https://www.sciencedirect.com/science/article/pii/S0304397505003373), and the other is a new proof that makes use of the Yoneda lemma. We have proved this result for the case of generalised containers, which are parameterised by an arbitrary category $\underline{\mathbf{C}}$ and give rise to functors of type $\underline{\mathbf{C}} \to \underline{\mathbf{Set}}$.
- **InductiveContainers.agda**: (WIP) Formalisation of the proofs that ordinary container functors are closed under fixed points, i.e. fixed points of container functors are themselves container functors. Proofs taken from [Containers: Constructing strictly positive types](https://www.sciencedirect.com/science/article/pii/S0304397505003373).
- **IndexedGeneralised.agda**: Proof that indexed containers are a special case of generalised containers.

An HTML rendering of this code can be found [here](https://stefaniatadama.com/agda_html/GeneralisedContainers.html).
