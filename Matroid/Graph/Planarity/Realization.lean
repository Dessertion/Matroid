import Matroid.Graph.Finite
import Matroid.Graph.GraphLike.ArbRel
import Mathlib.Logic.Relation
import Mathlib.Topology.Constructions
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Order
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Topology.Compactness.Compact

namespace Graph

variable {α β : Type*} {G : Graph α β}

open Set Function TopologicalSpace Topology Relation UniformSpace Sum
open scoped unitInterval

/-!
# Topological realization of a multigraph

The *geometric realization* `Graph.Realization G` is a 1-dimensional space: the discrete 0-skeleton
on `V(G)`, a closed 1-cell `I = Icc 0 1` per edge, and the quotient identifying `0`/`1` with chosen
endpoints of each edge (via `Classical.choice` among the two `IsLink` orientations).

This matches `sk₁` of a relative CW complex with stationary higher skeleta.  Concretely it is the
quotient of `V(G) ⊔ ⨆_{e ∈ E(G)} I`, i.e. (up to canonical homeomorphism) the pushout in `Top` of
`Fin 2 × E(G)` against the disjoint union of 1-disks.

`DiscreteVtx G` is used so the 0-skeleton carries the discrete topology `⊥`, not the subspace
topology from `α`.

If `G` is finite (finitely many vertices and edges), then `PreRealization G` is a finite disjoint
union of compact pieces (finite discrete spaces and copies of `I`), hence compact, and so is the
quotient `Realization G` (`Quotient.compactSpace`).
-/

/-- Vertices of `G` as a type, equipped with the discrete topology (the 0-skeleton). -/
def DiscreteVtx (G : Graph α β) := V(G)

/-- Discrete uniformity (hence discrete topology) on vertices. -/
instance instUniformSpaceDiscreteVtx (G : Graph α β) : UniformSpace (DiscreteVtx G) := ⊥

instance : DiscreteTopology (DiscreteVtx G) := discreteTopology_bot _

def DiscreteEdge (G : Graph α β) := E(G)

instance instUniformSpaceDiscreteEdge (G : Graph α β) : UniformSpace (DiscreteEdge G) := ⊥

instance : DiscreteTopology (DiscreteEdge G) := discreteTopology_bot _

instance instFiniteDiscreteVtx [G.Finite] : Finite (DiscreteVtx G) :=
  Finite.to_subtype G.vertexSet_finite

instance instFiniteDiscreteEdge [G.Finite] : Finite (DiscreteEdge G) :=
  Finite.to_subtype G.edgeSet_finite

noncomputable def DiscreteEdge.src (e : DiscreteEdge G) : DiscreteVtx G :=
  ⟨G.src e.prop, G.src_mem e.prop⟩

noncomputable def DiscreteEdge.tgt (e : DiscreteEdge G) : DiscreteVtx G :=
  ⟨G.tgt e.prop, G.tgt_mem e.prop⟩

/-- Disjoint union of the discrete 0-skeleton and one copy of `EdgeDisk` per edge. -/
def PreRealization (G : Graph α β) : Type _ :=
  DiscreteVtx G ⊕ (DiscreteEdge G × I)

instance instUniformSpacePreRealization (G : Graph α β) : UniformSpace (PreRealization G) :=
  Sum.instUniformSpace

/-- The topology induced by the sum uniformity agrees with the disjoint-union topology. -/
theorem preRealization_topology_eq_sum (G : Graph α β) :
    @UniformSpace.toTopologicalSpace (PreRealization G) (instUniformSpacePreRealization G) =
      @instTopologicalSpaceSum (DiscreteVtx G) (DiscreteEdge G × I) _ _ :=
  rfl

theorem uniformContinuous_preRealization_inl (G : Graph α β) :
    UniformContinuous (Sum.inl : DiscreteVtx G → PreRealization G) :=
  uniformContinuous_inl

theorem uniformContinuous_preRealization_inr (G : Graph α β) :
    UniformContinuous (Sum.inr : DiscreteEdge G × I → PreRealization G) :=
  uniformContinuous_inr

/-- Gluing relation for a single attachment: each endpoint of `EdgeDisk` is identified with the
corresponding vertex of `G`. -/
def glueRel (G : Graph α β) (x y : PreRealization G) : Prop :=
  (∃ e : E(G), x = Sum.inl (DiscreteEdge.src e) ∧ y = Sum.inr ⟨e, 0⟩) ∨
  (∃ e : E(G), x = Sum.inl (DiscreteEdge.tgt e) ∧ y = Sum.inr ⟨e, 1⟩)

/-- Topological realization: quotient of `PreRealization G` by the equivalence closure of
`glueRel`. -/
def Realization (G : Graph α β) : Type _ :=
  Quotient (EqvGen.setoid (glueRel G))

/-- Inclusion of a vertex into the realization. -/
def vertexMk (v : DiscreteVtx G) : Realization G :=
  Quotient.mk' (s := EqvGen.setoid (glueRel G)) (Sum.inl v)

/-- Inclusion of a point of the `e`-th edge interval into the realization. -/
def edgeMk (e : E(G)) (t : I) : Realization G :=
  Quotient.mk' (s := EqvGen.setoid (glueRel G)) (Sum.inr ⟨e, t⟩)

theorem glueRel_vertex_zero (e : E(G)) :
    EqvGen (glueRel G) (Sum.inl (DiscreteEdge.src e)) (Sum.inr ⟨e, 0⟩) :=
  EqvGen.rel _ _ <| Or.inl ⟨e, rfl, rfl⟩

theorem glueRel_vertex_one (e : E(G)) :
    EqvGen (glueRel G) (Sum.inl (DiscreteEdge.tgt e)) (Sum.inr ⟨e, 1⟩) :=
  EqvGen.rel _ _ <| Or.inr ⟨e, rfl, rfl⟩

theorem realization_eq_edgeMk_zero (e : E(G)) : vertexMk (DiscreteEdge.src e) = edgeMk e 0 :=
  Quotient.sound (glueRel_vertex_zero e)

theorem realization_eq_edgeMk_one (e : E(G)) : vertexMk (DiscreteEdge.tgt e) = edgeMk e 1 :=
  Quotient.sound (glueRel_vertex_one e)

instance : TopologicalSpace (Realization G) :=
  instTopologicalSpaceQuotient

theorem continuous_vertexMk : Continuous (vertexMk (G := G)) :=
  continuous_quotient_mk'.comp continuous_inl

theorem continuous_edgeMk (e : E(G)) : Continuous (fun t : I ↦ edgeMk e t) :=
  continuous_quotient_mk'.comp <| continuous_inr.comp
  <| continuous_prodMk.mpr ⟨continuous_const, continuous_inclusion subset_rfl⟩

/-- The pre-realization is compact when `G` is finite: finite disjoint union of compact spaces.

TC synthesis does not match `def PreRealization` to the `CompactSpace` instance for binary `Sum`;
we spell the disjoint union and reuse `inferInstance` there. -/
instance instCompactSpacePreRealization [G.Finite] : CompactSpace (PreRealization G) :=
  (inferInstance : CompactSpace (DiscreteVtx G ⊕ (DiscreteEdge G × I)))

/-- The topological realization of a finite multigraph is compact (quotient of a compact space). -/
instance instCompactSpaceRealization [G.Finite] : CompactSpace (Realization G) :=
  (inferInstance : CompactSpace (Quotient (EqvGen.setoid (glueRel G))))

theorem realization_isCompact_univ [G.Finite] : IsCompact (univ : Set (Realization G)) :=
  CompactSpace.isCompact_univ

end Graph
