/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Sym.Sym2
public import Matroid.Graph.GraphLike.Basic

/-!
# Dart graphs (half-edges)

Vertices and darts, with a fixed-point-free involution pairing darts into undirected edges.
-/

@[expose] public section

variable {α β : Type*} {x y z u v w : α} {a b c d : β} {e f : Sym2 β}

open Set Sym2 GraphLike

structure Graph (α β : Type*) where
  vertexSet : Set α
  halfEdgeSet : Set β
  inc : halfEdgeSet → α
  inc_mem {a : β} (h : a ∈ halfEdgeSet) : inc ⟨a, h⟩ ∈ vertexSet
  inv : β → β
  inv_invol {a : β} : inv (inv a) = a
  inv_ne {a : β} : inv a ≠ a
  inv_mem {a : β} (h : a ∈ halfEdgeSet) : inv a ∈ halfEdgeSet

-- initialize_simps_projections Graph (IsLink → isLink)

namespace Graph

variable {G H : Graph α β}

/-- `V(G)` denotes the `vertexSet` of a graph `G`. -/
scoped notation "V(" G ")" => Graph.vertexSet G

/-- `H(G)` denotes the `halfEdgeSet` of a graph `G`. -/
scoped notation "H(" G ")" => Graph.halfEdgeSet G

/-- The edge containing a half-edge `e`. -/
def edge (G : Graph α β) (a : β) : Sym2 β := s(a, inv G a)

def edgeSet (G : Graph α β) : Set (Sym2 β) := edge G '' H(G)

def inc' (G : Graph α β) : H(G) → V(G) := fun h ↦ ⟨G.inc h, G.inc_mem h.prop⟩

def inv' (G : Graph α β) : H(G) → H(G) := fun h ↦ ⟨G.inv h, G.inv_mem h.prop⟩

@[simp]
theorem inc'_coe (G : Graph α β) (b : H(G)) : (G.inc' b).val = G.inc b :=
  rfl

@[simp]
theorem inv'_val (G : Graph α β) (b : H(G)) : (G.inv' b).val = G.inv b.val :=
  rfl

@[simp]
theorem inv'_inv' (G : Graph α β) (b : H(G)) : G.inv' (G.inv' b) = b := by
  ext
  simp [inv', G.inv_invol]

def isLink (G : Graph α β) (e : Sym2 β) (x y : α) : Prop :=
  ∃ a, edge G a.val = e ∧ G.inc a = x ∧ G.inc (G.inv' a) = y

/-- The dart oriented from the half-edge `b` toward `G.inv b.val`. -/
def dartOf (G : Graph α β) (b : H(G)) : (β × α) × (β × α) :=
  ((b.val, (G.inc' b).val), (G.inv b.val, (G.inc' (G.inv' b)).val))

/-! ### Edges as unordered dart pairs -/

@[simp]
theorem edge_inv (G : Graph α β) (a : β) : edge G (G.inv a) = edge G a := by
  simp [edge, G.inv_invol, eq_swap]

@[simp]
theorem mem_edge_iff (G : Graph α β) (b a : β) : b ∈ edge G a ↔ b = a ∨ b = G.inv a := by
  simp [edge, mem_iff]

@[simp]
theorem forall_mem_edge_iff {P : β → Prop} : (∀ b ∈ edge G a, P b) ↔ P a ∧ P (G.inv a) :=
  forall_mem_pair

theorem mem_halfEdgeSet_of_mem_edge (ha : a ∈ H(G)) (hb : b ∈ edge G a) : b ∈ H(G) :=
  forall_mem_edge_iff.mpr ⟨ha, G.inv_mem ha⟩ b hb

/-! ### The edge set -/

theorem mem_edgeSet_iff : e ∈ edgeSet G ↔ ∃ a ∈ H(G), edge G a = e := by
  simp [edgeSet, mem_image]

theorem edge_mem_edgeSet (ha : a ∈ H(G)) : edge G a ∈ edgeSet G :=
  mem_image_of_mem _ ha

/-! ### Incidence predicate `isLink` -/

instance : Std.Symm (G.isLink e) where
  symm x y h := by
    obtain ⟨a, he, hx, hy⟩ := h
    refine ⟨G.inv' a, ?_, hy, ?_⟩
    · rw [← he]
      simp [inv'_val, edge_inv]
    · simpa [inv'_inv'] using hx

@[symm] theorem isLink.symm (h : isLink G e x y) : isLink G e y x := symm_of (G.isLink e) h

theorem isLink_comm : isLink G e x y ↔ isLink G e y x := ⟨isLink.symm, isLink.symm⟩

theorem isLink_of_mem_edge (ha : a ∈ H(G)) :
    isLink G (edge G a) (G.inc ⟨a, ha⟩) (G.inc (G.inv' ⟨a, ha⟩)) := by
  refine ⟨⟨a, ha⟩, rfl, rfl, rfl⟩

theorem isLink.mem_edgeSet (h : isLink G e x y) : e ∈ edgeSet G := by
  obtain ⟨a, he, -, -⟩ := h
  rw [← he]
  exact edge_mem_edgeSet a.prop

theorem edge_not_isDiag (G : Graph α β) (a : β) : ¬(edge G a).IsDiag := by
  simp only [edge, mk_isDiag_iff]
  exact fun h => G.inv_ne h.symm

/-- For a dart `a` and its partner `G.inv a`, the corresponding edge links their endpoints. -/
theorem isLink_edge (ha : a ∈ H(G)) :
    isLink G (edge G a) (G.inc ⟨a, ha⟩) (G.inc ⟨G.inv a, G.inv_mem ha⟩) := by
  have hsub : (⟨G.inv a, G.inv_mem ha⟩ : H(G)) = G.inv' ⟨a, ha⟩ := Subtype.ext rfl
  rw [congrArg G.inc hsub]
  exact isLink_of_mem_edge ha

/-! ### The graph-like structure -/

instance : DartLike α ((β × α) × (β × α)) where
  fst a := a.1.2
  snd a := a.2.2

instance : GraphLike α ((β × α) × (β × α)) (Graph α β) where
  verts G := V(G)
  darts G := Set.range (dartOf G)
  fst_mem_of_darts {G d} h := by
    obtain ⟨b, rfl⟩ := h
    simpa [dartOf, DartLike.fst] using (G.inc' b).prop
  snd_mem_of_darts {G d} h := by
    obtain ⟨b, rfl⟩ := h
    simpa [dartOf, DartLike.snd] using (G.inc' (G.inv' b)).prop
  Adj G u v := ∃ b : H(G), (G.inc' b).val = u ∧ (G.inc' (G.inv' b)).val = v
  exists_darts_iff_adj {G u v} := by
    constructor
    · rintro ⟨d, ⟨b, rfl⟩, rfl, rfl⟩
      refine ⟨b, ?_, ?_⟩ <;> simp [dartOf, DartLike.fst, DartLike.snd]
    · rintro ⟨b, rfl, rfl⟩
      refine ⟨dartOf G b, ⟨b, rfl⟩, ?_, ?_⟩ <;> simp [dartOf, DartLike.fst, DartLike.snd]

instance (G : Graph α β) : Std.Symm (Adj G) where
  symm _ _ := fun ⟨b, hu, hv⟩ ↦ ⟨G.inv' b, hv, by simpa [inv'_inv'] using hu⟩

theorem adj_iff_exists_isLink_edge {G : Graph α β} {u v : α} :
    Adj G u v ↔ ∃ a ∈ H(G), isLink G (edge G a) u v := by
  constructor
  · rintro ⟨b, rfl, rfl⟩
    exact ⟨b.val, b.prop, isLink_of_mem_edge b.prop⟩
  · rintro ⟨a, ha, b, he, rfl, rfl⟩
    exact ⟨b, by simp [inc'_coe], by simp [inc'_coe]⟩

end Graph
