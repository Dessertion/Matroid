import Matroid.Graph.Planarity.Realization
import Matroid.Graph.Connected.Defs
import Matroid.Graph.Walk.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Constructions

/-!
# Path-connectedness of graph realization

For a multigraph `G`, the combinatorial notion `Graph.Preconnected` (existence of a walk between
any two vertices) implies `PathConnectedSpace` on `Graph.Realization G`.

The construction uses explicit `Path`s in the quotient via `edgeMk` and `Path.trans`.  Extracting a
combinatorial walk from an arbitrary continuous path (the converse direction) is left to future
work; it requires a finite subdivision / covering argument on the CW-style quotient.
-/

namespace Graph

variable {α β : Type*} {G : Graph α β}

open scoped unitInterval
open Topology Path WList Relation

lemma continuous_mul_left_I (t : I) : Continuous (fun s : I => t * s) :=
  Continuous.codRestrict (s := I) ((continuous_const_mul (t : ℝ)).comp continuous_subtype_val)
    fun (s : I) => by
      obtain ⟨t, ht1, ht2⟩ := t
      obtain ⟨s, hs1, hs2⟩ := s
      simp [mul_le_one₀ ht2 hs1 hs2, Left.mul_nonneg ht1 hs1]

/-- Quotient map from the disjoint union `PreRealization G`. -/
def realMk (a : PreRealization G) : Realization G :=
  Quotient.mk' (s := EqvGen.setoid (glueRel G)) a

/-- The canonical path along an edge `e` in the realization, from `src e` to `tgt e`. -/
noncomputable def pathAlongEdge (e : E(G)) :
    Path (vertexMk (DiscreteEdge.src e)) (vertexMk (DiscreteEdge.tgt e)) where
  toContinuousMap := ⟨fun t : I ↦ edgeMk e t, continuous_edgeMk e⟩
  source' := (realization_eq_edgeMk_zero e).symm
  target' := (realization_eq_edgeMk_one e).symm

theorem joined_vertexMk_of_isLink {e : β} {x y : α} (h : G.IsLink e x y) :
    Joined (vertexMk ⟨x, h.left_mem⟩) (vertexMk ⟨y, h.right_mem⟩) := by
  let he := h.edge_mem
  have hst := G.isLink_src_tgt he
  let ed : E(G) := ⟨e, he⟩
  cases (h.eq_and_eq_or_eq_and_eq hst) with
  | inl hp =>
    simpa [hp.1, hp.2, DiscreteEdge.src, DiscreteEdge.tgt, ed] using
      (show Joined (vertexMk (DiscreteEdge.src ed)) (vertexMk (DiscreteEdge.tgt ed)) from
        ⟨pathAlongEdge ed⟩)
  | inr hp =>
    simpa [hp.1, hp.2, DiscreteEdge.src, DiscreteEdge.tgt, ed] using
      (show Joined (vertexMk (DiscreteEdge.tgt ed)) (vertexMk (DiscreteEdge.src ed)) from
        ⟨pathAlongEdge ed |>.symm⟩)

theorem joined_vertexMk_of_isWalk {w : WList α β} (hw : G.IsWalk w) :
    Joined (vertexMk ⟨w.first, hw.first_mem⟩) (vertexMk ⟨w.last, hw.last_mem⟩) := by
  induction hw with
  | @nil x hx => exact Joined.refl _
  | @cons x e w hw' hlink ih => simpa [last_cons] using (joined_vertexMk_of_isLink hlink).trans ih

theorem joined_vertexMk_of_connBetween {x y : α} (h : G.ConnBetween x y) :
    Joined (vertexMk ⟨x, h.left_mem⟩) (vertexMk ⟨y, h.right_mem⟩) := by
  obtain ⟨w, hw, rfl, rfl⟩ := h
  exact joined_vertexMk_of_isWalk hw

/-- From `src e`, follow the edge only up to parameter `t`. -/
lemma mul_one_I (t : I) : t * (1 : I) = t :=
  Subtype.ext (by simp [mul_one])

noncomputable def pathAlongEdgeTo (e : E(G)) (t : I) :
    Path (vertexMk (DiscreteEdge.src e)) (edgeMk e t) where
  toContinuousMap :=
    ⟨fun s : I ↦ edgeMk e (t * s), (continuous_edgeMk e).comp (continuous_mul_left_I t)⟩
  source' := by simp [realization_eq_edgeMk_zero]
  target' := by simp [mul_one_I t]

theorem joined_vertexMk_edgeMk (e : E(G)) (t : I) :
    Joined (vertexMk (DiscreteEdge.src e)) (edgeMk e t) :=
  ⟨pathAlongEdgeTo e t⟩

theorem joined_vertexMk_realMk_of_preconnected {v0 : α} (hv0 : v0 ∈ V(G)) (hG : G.Preconnected)
    (a : PreRealization G) : Joined (vertexMk ⟨v0, hv0⟩) (realMk a) := by
  cases a with
  | inl v =>
    simpa [realMk] using joined_vertexMk_of_connBetween (hG v0 v hv0 v.prop)
  | inr p =>
    obtain ⟨e, t⟩ := p
    refine Joined.trans (joined_vertexMk_of_connBetween (hG v0 (G.src e.prop) hv0 ?_)) ?_
    · exact (G.isLink_src_tgt e.prop).left_mem
    · simpa [realMk, DiscreteEdge.src] using joined_vertexMk_edgeMk e t

theorem pathConnectedSpace_of_connected (h : G.Connected) : PathConnectedSpace (Realization G) := by
  obtain ⟨v0, hv0⟩ := h.nonempty
  refine ⟨⟨vertexMk ⟨v0, hv0⟩⟩, ?_⟩
  intro x y
  refine Quotient.inductionOn₂ x y fun a b ↦ ?_
  exact (joined_vertexMk_realMk_of_preconnected hv0 h.pre a).symm.trans
    (joined_vertexMk_realMk_of_preconnected hv0 h.pre b)

/-!
### Converse (combinatorial walk from a topological path)

A continuous path `γ : I → Realization G` has compact image.  One can cover `Realization G` by open
sets meeting only finitely many cells, extract a finite subcover, and read off a finite edge
sequence.  Formalizing this requires additional lemmas on the quotient topology.
-/

theorem connected_of_pathConnectedSpace [PathConnectedSpace (Realization G)] :
    G.Connected := by
  rw [connected_iff]
  constructor
  · /- `Realization G` is path-connected so nonempty. An arbitrary point `x` is in either `V(G)`
    or somewhere on an edge. An edge must be incident to a vertex so in either case, there is a
    vertex in `G`. -/
    sorry
  classical
  intro x y hx hy
  sorry

theorem preconnected_iff_pathConnectedSpace_realization :
    G.Connected ↔ PathConnectedSpace (Realization G) :=
  ⟨pathConnectedSpace_of_connected, fun _ => connected_of_pathConnectedSpace⟩

end Graph
