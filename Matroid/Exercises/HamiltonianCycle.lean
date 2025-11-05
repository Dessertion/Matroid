import Mathlib.Tactic
import Mathlib.Data.Set.Finite.Basic

import Matroid.Graph.Walk.Path
import Matroid.Graph.Walk.Cycle
import Matroid.Graph.Degree.Basic
import Matroid.Graph.Finite
import Matroid.Graph.Subgraph.Basic
import Matroid.Graph.Connected.Defs
import Matroid.Graph.Connected.Component

import Qq open Qq Lean Meta Elab Tactic
-- simple is still broken
-- import Matroid.Graph.Simple

-- connectivity is still broken
-- import Matroid.Graph.Connected.Component

open WList Set

-- we will be using a lot of LEM...
open Classical


section NonGraphThings

variable {α : Type*}

lemma finite_of_ncard_nonzero {s : Set α} (h : s.ncard ≠ 0) : s.Finite := by
  by_contra hyp
  replace hyp : s.Infinite := hyp
  apply h
  exact Infinite.ncard hyp

lemma finite_of_ncard_positive {s : Set α} (h : 0 < s.ncard) : s.Finite := by
  apply finite_of_ncard_nonzero ; linarith

lemma minimal_is_lower_bound [LinearOrder α] {P : α → Prop} {x : α} (h : Minimal P x) :
    ∀ y, P y → x ≤ y := by
  intro y hy
  simp [Minimal] at h
  obtain (_|_) := le_total x y
  · assumption
  · tauto

lemma minimalFor_is_lower_bound
    {ι} [LinearOrder α] {P : ι → Prop} (f : ι → α) {i : ι} (h : MinimalFor P f i) :
    ∀ j, P j → f i ≤ f j := by
  intro j hj
  simp [MinimalFor] at h
  obtain (_|_) := le_total (f i) (f j)
  · assumption
  · tauto

lemma maximal_is_upper_bound [LinearOrder α] {P : α → Prop} {x : α} (h : Maximal P x) :
    ∀ y, P y → y ≤ x := by
  intro y hy
  simp [Maximal] at h
  obtain (_|_) := le_total y x
  · assumption
  · tauto

lemma maximalFor_is_upper_bound
    {ι} [LinearOrder α] {P : ι → Prop} (f : ι → α) {i : ι} (h : MaximalFor P f i) :
    ∀ j, P j → f j ≤ f i := by
  intro j hj
  simp [MaximalFor] at h
  obtain (_|_) := le_total (f j) (f i)
  · assumption
  · tauto

end NonGraphThings

namespace WList

variable {α β : Type*} {x y z u v : α} {e f : β} {w : WList α β}

-- this is probably a bad idea, but let's test it first and see *how* bad it can get
def getEdge? : WList α β → ℕ → Option β
  | nil _, _ => none
  | cons _ e _, 0 => some e
  | cons _ _ w, n + 1 => w.getEdge? n

@[simp]
lemma getEdge?_nil (x : α) (n : ℕ) : (nil x (β := β)).getEdge? n = none := rfl

@[simp]
lemma getEdge?_cons_zero (x e) (w : WList α β) : (cons x e w).getEdge? 0 = some e := rfl

@[simp]
lemma getEdge?_cons_succ (x e) (w : WList α β) (n : ℕ) :
    (cons x e w).getEdge? (n + 1) = w.getEdge? n := rfl

@[simp]
lemma getEdge?_eq_none_of_length_le {n} (hn : w.length ≤ n) : w.getEdge? n = none := by
  induction w generalizing n with
  | nil _ => simp
  | cons _ _ _ => induction n with simp_all

@[simp]
lemma getEdge?_isNone_of_length_le {n} (hn : w.length ≤ n) : (w.getEdge? n).isNone := by
  simp [getEdge?_eq_none_of_length_le hn]

@[simp]
lemma lt_length_of_getEdge?_isSome (w : WList α β) (n : ℕ) (h : (w.getEdge? n).isSome) :
    n < w.length := by
  by_contra! hyp
  rw [getEdge?_eq_none_of_length_le hyp] at h
  exact (Bool.eq_not_self none.isSome).mp h

lemma exists_of_getEdge?_lt_length (w : WList α β) {n} (hn : n < w.length) :
    ∃ f, w.getEdge? n = some f ∧ f ∈ w.edge := by
  induction n generalizing w with
  | zero => cases w <;> simp_all
  | succ n IH =>
    cases w with simp_all
    | cons x e w =>
      obtain ⟨e, he⟩ := IH _ hn
      use e; tauto

lemma exists_mem_of_getEdge?_isSome (w : WList α β) (n : ℕ) (h : (w.getEdge? n).isSome) :
    ∃ e, w.getEdge? n = some e ∧ e ∈ w.edge := by
  apply exists_of_getEdge?_lt_length
  apply lt_length_of_getEdge?_isSome; assumption

lemma getEdge?_eq_getElem?_edge (w : WList α β) (n : ℕ) : w.getEdge? n = w.edge[n]? := by
  induction n generalizing w with
  | zero => cases w <;> simp_all
  | succ n IH => cases w with simp_all

lemma mem_of_getEdge? (w : WList α β) (n : ℕ) {f} (h : w.getEdge? n = some f) :
    f ∈ w.edge := by
  rw [getEdge?_eq_getElem?_edge] at h
  exact List.mem_of_getElem? h

variable [DecidableEq β]

-- returns the index of the edge, equal to `w.length` if the edge doesn't appear
def idxOfEdge : WList α β → β → ℕ
  | nil _, _ => 0
  | cons _ e' w, e =>
    if e = e' then 0 else w.idxOfEdge e + 1

@[simp]
lemma idxOfEdge_nil (u : α) (e : β) : (nil u (β := β)).idxOfEdge e = 0 := rfl

@[simp]
lemma idxOfEdge_cons (u e) (w : WList α β) :
    (cons u e w).idxOfEdge f = if f = e then 0 else w.idxOfEdge f + 1 := rfl

@[simp]
lemma idxOfEdge_cons_self (u e) (w : WList α β) :
    (cons u e w).idxOfEdge e = 0 := by simp [idxOfEdge_cons]

@[simp]
lemma idxOfEdge_cons_ne (hne : f ≠ e)  :
    (cons u e w).idxOfEdge f = w.idxOfEdge f + 1 := by
  simp [idxOfEdge_cons, hne]

lemma idxOfEdge_notMem (hf : f ∉ w.edge) : w.idxOfEdge f = w.length := by
  induction w with
  | nil => simp
  | cons u e w IH =>
    simp at hf
    rw [←ne_eq] at hf
    specialize IH hf.2
    rw [idxOfEdge_cons_ne hf.1]; try assumption
    simp [IH]

lemma eq_or_ne_mem_of_mem_cons_edge (h : f ∈ (cons u e w).edge) :
    f = e ∨ (f ≠ e ∧ f ∈ w.edge) := by
  obtain rfl | hne := Decidable.eq_or_ne f e ; simp
  right; refine ⟨hne, ?_⟩
  simp_all

lemma idxOfEdge_mem_le (hf : f ∈ w.edge) : w.idxOfEdge f < w.length := by
  induction w with
  | nil => simp_all
  | cons u e w IH =>
    obtain rfl | ⟨hne, hfw⟩ := eq_or_ne_mem_of_mem_cons_edge hf; simp; clear hf
    specialize IH hfw
    rw [idxOfEdge_cons_ne ‹_›, cons_length]
    linarith

lemma idxOfEdge_eq_idxOf_edge (w : WList α β) (f : β) : w.idxOfEdge f = w.edge.idxOf f := by
  induction w with
  | nil => simp
  | cons u e w IH =>
    obtain rfl | hne := Decidable.eq_or_ne f e; simp
    simp [idxOfEdge_cons_ne ‹_›, IH, List.idxOf_cons_ne _ hne.symm]

lemma getEdge?_idxOfEdge (w : WList α β) (hfw : f ∈ w.edge) :
    w.getEdge? (w.idxOfEdge f) = some f := by
  rwa [getEdge?_eq_getElem?_edge, idxOfEdge_eq_idxOf_edge, List.getElem?_idxOf]


lemma existsUnique_of_getEdge?_lt_length' (hw : w.edge.Nodup) {n} (hn : n < w.length) :
    ∃! f, w.getEdge? n = some f ∧ w.idxOfEdge f = n := by
  induction n generalizing w with
  | zero =>
    cases w with simp_all
    | cons x e w => use e; simp
  | succ n IH =>
    cases w with simp_all
    | cons x e w =>
      obtain ⟨f, hf, hf_unique⟩ := IH hw.2 hn
      refine ⟨f, ?_, by simp_all⟩
      simp
      refine ⟨hf.1, ?_⟩
      have hne : f ≠ e := by
        by_contra! rfl
        have := w.mem_of_getEdge? _ hf.1
        tauto
      rw [if_neg (by rwa [←ne_eq])]
      linarith

lemma idxOfEdge_getEdge? (hw : w.edge.Nodup) {n} (hn : n < w.length) :
    (w.getEdge? n).map w.idxOfEdge = some n := by
  have ⟨f', hf', hf'_unique⟩ := w.existsUnique_of_getEdge?_lt_length' hw hn
  simp_all


-- given an edge f, we return the left and right vertices of the first instance of
-- of f in w, defaulting to the last vertex if f is not in w
def adjVertices (w : WList α β) (f : β) : α × α :=
  ⟨w.get (w.idxOfEdge f), w.get (w.idxOfEdge f + 1)⟩

lemma adjVertices_eq_last_of_notMem (h : f ∉ w.edge) :
    w.adjVertices f = ⟨w.last, w.last⟩ := by
  simp [adjVertices, idxOfEdge_notMem h, get_of_length_le]

-- if it is a member, then it forms a DInc triplet
lemma dInc_adjVertices_of_mem (h : f ∈ w.edge) :
    let uu := w.adjVertices f;
    w.DInc f uu.1 uu.2 := by
  simp only [adjVertices]
  generalize n_def : w.idxOfEdge f = n
  induction w generalizing n with
  | nil => simp_all
  | cons x e w IH =>
    simp_all
    obtain rfl | hne := Decidable.eq_or_ne f e <;>
      (simp_all; subst n_def)
    · left; simp
    · right; simpa

-- in a WList with no repeated edges, each edge is part of exactly one DInc triplet
lemma dInc_iff_eq_of_dInc_of_edge_nodup (hw : w.edge.Nodup) (he : w.DInc e u v) :
    w.DInc e x y ↔ x = u ∧ y = v := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; assumption⟩
  induction w with
  | nil => simp_all
  | cons z f w IH =>
    simp at hw h he
    obtain ⟨rfl, rfl, rfl⟩ | h := h
    · obtain ⟨rfl, he, rfl⟩ | he := he; try tauto
      exfalso; apply hw.1; apply he.edge_mem
    obtain ⟨rfl, rfl, rfl⟩ | he := he
    · exfalso; apply hw.1; apply h.edge_mem
    apply IH <;> first | assumption | tauto

lemma existsUnique_dInc_of_mem_edge (hw : w.edge.Nodup) (he : e ∈ w.edge) :
    ∃! p : α × α, w.DInc e p.1 p.2 := by
  have ⟨x, y, hxy⟩ := exists_dInc_of_mem_edge he
  refine ⟨⟨x,y⟩, hxy, ?_⟩
  simp [dInc_iff_eq_of_dInc_of_edge_nodup hw hxy]

lemma dInc_iff_eq_of_dInc_of_vertex_nodup_left (hw : w.vertex.Nodup) (hu : w.DInc e u v) :
    w.DInc f u y ↔ f = e ∧ y = v := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; assumption⟩
  induction w with
  | nil _ => simp_all
  | cons u' f' w IH =>
    simp_all
    obtain ⟨rfl, rfl, rfl⟩ | h := h
    · obtain ⟨hu, rfl, rfl⟩ | hu := hu; try tauto
      exfalso; apply hw.1; apply hu.left_mem
    obtain ⟨rfl, rfl, rfl⟩ | hu := hu
    · exfalso; apply hw.1; apply h.left_mem
    apply IH <;> assumption

lemma dInc_iff_eq_of_dInc_of_vertex_nodup_right (hw : w.vertex.Nodup) (hv : w.DInc e u v) :
    w.DInc f x v ↔ f = e ∧ x = u := by
  generalize hw_def' : w.reverse = w'
  have hw' : w'.vertex.Nodup := by rwa [← hw_def', reverse_vertex, List.nodup_reverse]
  have hv' : w'.DInc e v u := by simpa [← hw_def']
  have := dInc_iff_eq_of_dInc_of_vertex_nodup_left (f := f) (v := u) (y := x) hw' hv'
  rwa [← hw_def', dInc_reverse_iff] at this

-- -- In a WList with no repeated vertices, each non-last vertex is part of exactly one DInc triplet
-- -- as the left vertex.
-- --
-- -- These two proofs are kinda awful, lol, surely there's a way to do this that's not just puking
-- -- commands at the screen until you get "goals accomplished".
-- -- In particular, this proof and the previous proof are *so* structurally similar,
-- -- but my brain is too off at the moment to come up with a coherent way to combine them.
-- lemma existsUnique_dInc_of_mem_left (hw : w.vertex.Nodup) (hxw : x ∈ w) (hx : x ≠ w.last) :
--     ∃! p : β × α, w.DInc p.1 x p.2 := by
--   induction w with
--   | nil => simp_all
--   | cons u e w IH =>
--     have hne : x ≠ w.last := by simpa
--     simp at hw
--     obtain (rfl|hxw) := by simpa using hxw
--     · refine ⟨⟨e, w.first⟩, ?_, ?_⟩ <;> simp_all
--       intros f y hyp
--       obtain (hyp|hyp) := hyp
--       · tauto
--       exfalso
--       apply hw.1
--       apply hyp.left_mem
--     · obtain ⟨p, hp, hp_unique⟩ := IH hw.2 hxw hne
--       refine ⟨p, ?_, ?_⟩
--       · simp only; apply DInc.cons; assumption
--       simp only at *
--       intros q hq
--       rw [dInc_cons_iff] at hq
--       obtain (hq|hq) := hq
--       · exfalso; apply hw.1; rwa [hq.1]
--       apply hp_unique; assumption

-- lemma existsUnique_dInc_of_mem_right (hw : w.vertex.Nodup) (hxw : x ∈ w) (hx : x ≠ w.first) :
--     ∃! p : β × α, w.DInc p.1 p.2 x := by
--   set w' := w.reverse
--   have hw'_vertex : w'.vertex = w.vertex.reverse := reverse_vertex
--   have hx' : x ≠ w'.last := by
--     rwa [reverse_last]
--   have hw'_nodup : w'.vertex.Nodup := by
--     rwa [hw'_vertex, List.nodup_reverse]
--   have hxw' : x ∈ w' := by rwa [mem_reverse]
--   have answer := existsUnique_dInc_of_mem_left hw'_nodup hxw' hx'
--   simp [w'] at answer
--   assumption

end WList

namespace Graph

variable {α β : Type*} [CompleteLattice α] {x y z u v : α} {e f : β} {G H : Graph α β}

/- Theorem 10.1.1 (Dirac 1952)
Every graph with n >= 3 vertices and minimum degree at least n/2 has a Hamiltonian cycle.
-/

-- INITIAL DEFINITIONS

def NeBot (G : Graph α β) : Prop :=
  G ≠ ⊥

@[simp]
lemma NeBot_iff_vertexSet_nonempty {G : Graph α β} :
    G.NeBot ↔ V(G).Nonempty := by
  simp [NeBot]

lemma vertexSet_nonempty_of_NeBot {G : Graph α β} (h : G.NeBot) :
    V(G).Nonempty := by
  rwa [←NeBot_iff_vertexSet_nonempty]

lemma NeBot_iff_encard_positive {G : Graph α β} :
    G.NeBot ↔ 0 < V(G).encard := by
  simp

lemma NeBot_of_ncard_positive {G : Graph α β} (h : 0 < V(G).ncard) : G.NeBot := by
  rw [NeBot, ne_eq, ←vertexSet_eq_empty_iff, ←ne_eq, ←Set.nonempty_iff_ne_empty]
  apply nonempty_of_ncard_ne_zero
  linarith

def degreeSet (G : Graph α β) : Set ℕ :=
  G.degree '' V(G)

@[simp]
lemma degreeSet_eq {G : Graph α β} :
    G.degreeSet = G.degree '' V(G) := rfl

lemma degreeSet_finite_of_finite {G : Graph α β} (hFinite : G.Finite) :
    G.degreeSet.Finite := by
  simp [degreeSet]
  refine Set.Finite.image ?_ ?_
  exact vertexSet_finite

lemma degreeSet_finite (G : Graph α β) [G.Finite] : G.degreeSet.Finite :=
  degreeSet_finite_of_finite ‹_›

lemma degreeSet_nonempty {G : Graph α β} (hNeBot : G ≠ ⊥) : G.degreeSet.Nonempty := by
  simpa [degreeSet]

-- lemma exists_minDegreeVx (G : Graph α β) (hFinite : G.Finite) (hNeBot : G.NeBot) :
--     ∃ v, MinimalFor (· ∈ V(G)) G.degree v := by
--   refine Set.Finite.exists_minimalFor G.degree V(G) vertexSet_finite ?_
--   apply vertexSet_nonempty_of_NeBot; trivial

-- noncomputable def minDegreeVx (G : Graph α β) : α :=
--   open Classical in
--   if h : G.Finite ∧ G.NeBot then
--     Classical.choose (G.exists_minDegreeVx h.1 h.2)
--   else
--     ∅

-- G.minDegree returns the minimum degree of its vertices if G is finite, else it returns 0
noncomputable def minDegree (G : Graph α β) : ℕ :=
  open Classical in
  if h : G.Finite ∧ G.NeBot then
    Classical.choose <|
    Set.Finite.exists_minimal (degreeSet_finite_of_finite h.1) (degreeSet_nonempty h.2)
  else 0

-- this is the price we pay for choice
@[simp]
lemma minDegree_eq (G : Graph α β) (hFinite : G.Finite) (hNeBot : G.NeBot) :
    G.minDegree =
    (Classical.choose <|
    Set.Finite.exists_minimal
      (degreeSet_finite_of_finite hFinite)
      (degreeSet_nonempty hNeBot)) := by
  have : G.Finite ∧ G.NeBot = True := by
    simp
    refine ⟨?_, ?_⟩ <;> assumption
  simp only [minDegree]
  simp only [this, and_self, ↓reduceDIte, degreeSet_eq, mem_image]

@[simp]
lemma minDegree_eq' (G : Graph α β) (h : ¬ (G.Finite ∧ G.NeBot)) :
    G.minDegree = 0 := by
  simp [minDegree]
  tauto

lemma minDegree_spec (G : Graph α β) (hFinite : G.Finite) (hNeBot : G.NeBot) :
    Minimal (· ∈ G.degreeSet) G.minDegree := by
  have hspec :=
    Classical.choose_spec <|
    Set.Finite.exists_minimal (degreeSet_finite_of_finite hFinite) (degreeSet_nonempty hNeBot)
  rw [minDegree_eq] <;> assumption

lemma exists_minDegreeVx (G : Graph α β) (hFinite : G.Finite) (hNeBot : G.NeBot) :
    ∃ v ∈ V(G), G.minDegree = G.degree v := by
  have ⟨⟨v, vspec⟩, dspec⟩ := G.minDegree_spec hFinite hNeBot
  use v
  tauto

-- minDegree is indeed a lower bound
lemma minDegree_le_degree (G : Graph α β) :
    ∀ v ∈ V(G), G.minDegree ≤ G.degree v := by
  intro v hv
  obtain (p|p) := Classical.em (G.Finite ∧ G.NeBot)
  · have hspec := G.minDegree_spec p.1 p.2
    suffices h : G.degree v ∈ G.degreeSet by
      refine minimal_is_lower_bound hspec ?_ ?_
      assumption
    simp
    use v
  · simp [G.minDegree_eq' p]

-- MORE THINGS

lemma degree_lt_vertexCount {G : Graph α β} [G.Simple] {v : α} (h : v ∈ V(G)) :
    G.degree v < V(G).ncard := by sorry

lemma minDegree_lt_vertexCount {G : Graph α β} [G.Simple] (hFinite : G.Finite) (hNeBot : G.NeBot) :
    G.minDegree < V(G).ncard := by
  have ⟨v,vspec⟩ := G.exists_minDegreeVx hFinite hNeBot
  rw [vspec.2]
  apply degree_lt_vertexCount
  tauto

--The exercises start here
--I added this lemma. Seems important. Do we need to prove it or already exists but is not working?
lemma isCompOf_subset (G H : Graph α β) (hHG : H.IsCompOf G) : V(H) ⊆ V(G) := by
  have hclo : H ≤c G := by
      --Richard already has a lemma for this
      exact IsCompOf.isClosedSubgraph hHG
  exact IsClosedSubgraph.vertexSet_mono hclo
  -- Use IsClosedSubgraph.vertexSet_mono to finsih


lemma minDegree_le_minDegree_of_isCompOf (G H : Graph α β) [G.Finite] (hHG : H.IsCompOf G) :
    G.minDegree ≤ H.minDegree := by
    obtain ⟨v, hv, hveq⟩ := H.exists_minDegreeVx
      (finite_of_le hHG.le)
      (NeBot_iff_vertexSet_nonempty.2 hHG.nonempty)
    rw [hveq]
    have hvG : v ∈ V(G) := by
      --I cheated and added the lemma above
      have hcheat : V(H) ⊆ V(G) := isCompOf_subset G H hHG
      -- Have should follow now
      exact hcheat hv
    have hclo : H ≤c G := by
      --Richard already has a lemma for this
      exact IsCompOf.isClosedSubgraph hHG
    have heq : H.degree v = G.degree v := by
      --Use IsClosedSubgraph.degree_eq
      exact IsClosedSubgraph.degree_eq hHG.isClosedSubgraph hv
    rw [heq]
    exact minDegree_le_degree G v hvG

  --Somhow I did this exercise instead
lemma minDegree_le_minDegree_of_Subgraph (G H : Graph α β) [G.Finite] (hHG : H ≤s G) :
    H.minDegree ≤ G.minDegree := by
    --The following two haves are used in the obtain.
    --First one follows from H being a component of a finite graph
  have Hfin: H.Finite := finite_of_le hHG.le
  obtain (hne | hni) := Classical.em (H.NeBot)
  · have gne : G.NeBot := by
      rw [NeBot_iff_vertexSet_nonempty]
      rw [NeBot_iff_vertexSet_nonempty] at hne
      have VHseVG : V(H) ⊆ V(G) := hHG.le.vertexSet_subset
      exact Nonempty.mono VHseVG hne
    obtain ⟨v, hv, hveq⟩ := H.exists_minDegreeVx Hfin hne
    rw [hveq]
    have hvG: v ∈ V(G) := hHG.le.vertexSet_subset hv
    obtain ⟨w, gw, gweq⟩ := G.exists_minDegreeVx ‹G.Finite› gne
    have wvH: w ∈ V(H) := by
      rw [hHG.vertexSet_eq]
      exact gw
    have h1 : H.degree w ≤ G.degree w := degree_mono hHG.le w
    rw [gweq]
    rw [← hveq]
    have h2 : H.minDegree ≤ H.degree w := minDegree_le_degree H w wvH
    linarith

  --This is the case the graph is empty. Richard has a nice lemma that if the graph is
  --empty or infinite then the min degree is 0. We just need to rw that
  rw [H.minDegree_eq' (not_and.mpr fun a ↦ hni)]
  exact Nat.zero_le G.minDegree

lemma ge_two_components_of_not_connected {G : Graph α β} (hNeBot : G.NeBot) (h : ¬ G.Connected) :
    2 ≤ G.Components.encard := by
  -- G has a vertex
  obtain ⟨ v, hv ⟩ := vertexSet_nonempty_of_NeBot hNeBot
  -- I cheated here, but this lemma is missing and I'm guessing it should be in connected
  obtain ⟨ H, hH, hvH ⟩ := G.exists_IsCompOf_vertex_mem hv
  have hbig : ∃ w ∈ V(G), w ∉ V(H) := by
    by_contra! hw
    --Our contradiction is that G is connected. The following have is the hardest.
    have hcon : G = H := by
    -- I think I went overboard on this refine, try refine ext_inc ?_ ?_ and see what happens
      refine ext_inc (Subset.antisymm_iff.mpr ⟨hw, isCompOf_subset G H hH ⟩  ) ?_
      intro e x
      -- Here is a one line proof, try to write this in steps.
      refine ⟨ fun hh ↦ (Inc.of_isClosedSubgraph_of_mem hh (IsCompOf.isClosedSubgraph hH)
          (hw x (Inc.vertex_mem hh))), fun hh ↦ (Inc.of_le hh (IsCompOf.le hH)) ⟩
    rw [ hcon ] at hH
    -- Just state the contradiction
    sorry
  obtain ⟨ w, hw, hwH ⟩ := hbig
  obtain ⟨ H₁, hH1, hvH1 ⟩ := G.exists_IsCompOf_vertex_mem hw
  have : H ≠ H₁ := by sorry
  sorry

def IsIndependent (G : Graph α β) (S : Set (α)) : Prop :=
  S ⊆ V(G) ∧ S.Pairwise (fun x y ↦ ¬ G.Adj x y)

def IndepNumLE (G : Graph α β) (n : ℕ∞) : Prop :=
  ∀ S, G.IsIndependent S → S.encard ≤ n

def IsMaxIndependent (G : Graph α β) (S : Set (α)) : Prop :=
  IsIndependent G S ∧ (∀ A, IsIndependent G A → A.ncard ≤ S.ncard )

def ConnectivityGE (G : Graph α β) (k : ℕ∞) : Prop :=
  ∀ S, S.encard < k → (G - S).Connected

--Avoids complete graph case but is not technically correct
def IsSepSet (G : Graph α β) (S : Set (α)) : Prop :=
  (S ⊆ V(G)) ∧ (¬ (G - S).Connected) ∧ (S ≠ V(G))

def IsMinSepSet (G : Graph α β) (S : Set (α)) : Prop :=
  IsSepSet G S  ∧ ( ∀ A, IsSepSet G A → S.ncard ≤ A.ncard )

lemma Bound_on_indepSet {G : Graph α β} [G.Simple]
    (S : Set (α)) (hS : IsSepSet G S)
    (H : Graph α β ) (hH : IsCompOf H (G-S) )
    (A : Set (α)) (hA : IsMaxIndependent G A) ( v : α ) (hx : v ∈ V(H) ∩ A )
    : G.degree v + (A ∩ V(H)).ncard ≤ (V(H)).ncard + S.ncard := by
    -- Need degree_eq_ncard_adj, will work after update
  let Inc := {w | G.Adj v w}
  let IncW := {w | G.Adj v w} ∩ V(H)

  --For the following you need that the sets are disjoint
  have hf1 : (Inc ∪ (A ∩ V(H))).ncard = Inc.ncard + (A ∩ V(H)).ncard := sorry
  have hf2 : (V(H) ∪ S).ncard = V(H).ncard + S.ncard := sorry
  --Use degree_eq_ncard_adj
  have hdeg : G.degree v = Inc.ncard := sorry
  --This one should be straight forward
  have h1 : Inc ∪ (A ∩ V(H)) = (IncW ∪ (A ∩ V(H))) ∪ (Inc\IncW) := sorry
  --Again, disjoint sets
  have hf3 : ((IncW ∪ (A ∩ V(H))) ∪ (Inc\IncW) ).ncard =
      (IncW ∪ (A ∩ V(H))).ncard + (Inc\IncW).ncard
    := sorry
  --Very important
  rw [←hf2,hdeg,←hf1,h1, hf3 ]

  --Inequalities to finish
  have hH : (IncW ∪ (A ∩ V(H))).ncard ≤ V(H).ncard := by
    have hH1 : (IncW ∪ (A ∩ V(H))) ⊆ V(H) := sorry
    sorry

  have hS : (Inc\IncW).ncard ≤ S.ncard := by
    have hH1 :(Inc\IncW) ⊆ S := sorry
    sorry
  linarith

--Again, is missing when G is complete but whatever
lemma indep_to_Dirac {G : Graph α β} [G.Simple] (h3 : 3 ≤ V(G).ncard)
    (S : Set (α)) (HS : IsMinSepSet G S )
    (A : Set (α)) (hA : IsMaxIndependent G A)
    (hDirac : V(G).ncard ≤ 2 * G.minDegree ) : A.ncard ≤ S.ncard := by
  --Important case
  obtain ( HAS| he ) := Decidable.em (A ⊆ S)
  · have : S.Finite := by sorry
    exact ncard_le_ncard HAS this
  have ⟨x, hxA, hvS ⟩ : ∃ x ∈ A, x ∉ S := by exact not_subset.mp he
  -- Add hDirac applyed to x. You won't need it immediatly but will need it in all cases

  --We want to use ge_two_components_of_not_connected with G-S so we need:
  have hxS: x ∈ V(G - S) := by sorry

  have hNeBotS : (G - S).NeBot := by
    apply NeBot_iff_vertexSet_nonempty.2
    sorry

  have hcomp := ge_two_components_of_not_connected hNeBotS sorry
  have ⟨ H1, hccH1, hcH1 ⟩ : ∃ H, IsCompOf H (G-S) ∧ x ∈ V(H) := by
    -- use (VertexConnected.refl x)
    sorry

  --Here are two options to finish the proof, either define H2 as follows, but it won't be conencted
  let H2 := G - (V(H1) ∪ S)
  --In this case use hcomp to get V(H2)≠ ∅

  --Second option is to use and prove this
  -- have ⟨ H2, hccH2, h12 ⟩  : ∃ H, IsCompOf H (G-S) ∧ H ≠ H1 := by
  --   sorry
  --see Richards proof using hcomp
  --In this case you will need (V(H2)).ncard ≤ (V(G)\ (V(H1) ∪ S) ).ncard + S.ncard (or something)

  -- Second annoying case
  obtain ( Hemp| hAH1 ) := Decidable.em ( A ∩ V(H2) = ∅)
  · have ⟨y, hy ⟩ : ∃ y, y ∈ V(H2) \ A := by sorry
    --Apply Bound_on_indepSet with modifications since H2 is not a connected component
    -- You will nee hDirac applied to y
    sorry

  --Easy case
  obtain ⟨y, yA2 ⟩ := nonempty_iff_ne_empty.mpr hAH1

  --Use Bound_on_indepSet twice and linarith to conclude. You'll also need
  have h1 : (V(H1)).ncard + S.ncard + (V(H2)).ncard + S.ncard = V(G).ncard + S.ncard := by sorry
  -- Add hDirac applied to y
  sorry

lemma finite_components_of_finite {G : Graph α β} (hFinite : G.Finite) :
  G.Components.Finite := by
  sorry

/- Step 1: WTS G is connected.
Proof: Suppose not. Then the degree of any vertex in the smallest component C of G
would be less than |C| ≤ n/2.
-/


lemma thm1_1_connected {G : Graph α β} [G.Simple] [hFinite : G.Finite]
  (hV : 3 ≤ V(G).ncard) (hDegree : V(G).ncard ≤ 2 * G.minDegree) :
  G.Connected := by
  have encard_eq_ncard : V(G).encard = ↑V(G).ncard := by
    rw [Set.Finite.cast_ncard_eq]
    exact vertexSet_finite
  have hNeBot : G.NeBot := by
    apply NeBot_of_ncard_positive
    linarith

  -- Suppose not.
  by_contra! hyp_contra

  -- There thus must be at least two components.
  have num_components_ge_2 : 2 ≤ G.Components.encard :=
    ge_two_components_of_not_connected hNeBot hyp_contra

  have components_nonempty : G.Components.Nonempty := by
    apply nonempty_of_encard_ne_zero
    intro h; rw [h] at num_components_ge_2; clear h
    norm_num at num_components_ge_2

  -- Choose the smallest component.
  obtain ⟨min_comp, min_comp_spec⟩ :=
    Set.Finite.exists_minimalFor
      (fun H => H.vertexSet.ncard)
      G.Components
      (finite_components_of_finite hFinite)
      components_nonempty

  -- There must be at least one other component.
  have ⟨other_comp, other_comp_spec⟩ :
    ∃ H, H.IsCompOf G ∧ H ≠ min_comp := by
    by_contra! hyp_contra
    have is_singleton : G.Components = {min_comp} := by
      exact (Nonempty.subset_singleton_iff components_nonempty).mp hyp_contra
    have : G.Components.encard = 1 := by
      simp [is_singleton]
    rw [this] at num_components_ge_2; clear this
    have : (2 : ℕ) ≤ (1 : ℕ) := by exact ENat.coe_le_coe.mp num_components_ge_2
    linarith

  -- G, min_comp, other_comp have finite vertexSets
  have G_finite_vertexSet : V(G).Finite := vertexSet_finite
  have min_comp_finite_vertexSet : V(min_comp).Finite := by
    suffices min_comp.Finite by exact vertexSet_finite
    exact Finite.mono hFinite min_comp_spec.1.le
  have other_comp_finite_vertexSet : V(other_comp).Finite := by
    suffices other_comp.Finite by exact vertexSet_finite
    exact Finite.mono hFinite other_comp_spec.1.le

  -- other_comp has at least as many vertices as min_comp
  have other_comp_larger : V(min_comp).ncard ≤ V(other_comp).ncard := by
    refine minimalFor_is_lower_bound (fun H : Graph α β => H.vertexSet.ncard) min_comp_spec ?_ ?_
    simp
    exact other_comp_spec.1
  -- min_comp and other_comp have disjoint vertex sets
  have disjoint_vx_sets : Disjoint V(min_comp) V(other_comp) := by
    suffices StronglyDisjoint min_comp other_comp by
      exact this.vertex
    apply G.components_pairwise_stronglyDisjoint <;> try tauto
    exact min_comp_spec.1

  have G_vertexSet_is_superset : V(min_comp) ∪ V(other_comp) ⊆ V(G) := by
    rw [union_subset_iff]; constructor <;> apply vertexSet_mono
    -- This works: it does exactly what the two following bulleted lines do:
    /-
     · exact min_comp_spec.1.le
     · exact other_comp_spec.1.le
    -/
    -- But it does so without referring to names explicitly.
    run_tacq
      for ldecl in ← getLCtx do
        let hyp := mkIdent ldecl.userName
        let some ty := ← checkTypeQ (← whnf ldecl.type) q(Prop) | continue
        if let ~q($p ∧ $q) := ty then
          evalTactic (← `(tactic| try exact $hyp.1.le))
    -- The type-checking is completely unnecessary, the following code would suffice as well:
    /-
    run_tacq
      for ldecl in ← getLCtx do
        let hyp := mkIdent ldecl.userName
        evalTactic (← `(tactic| try exact $hyp.1.le))
    -/
    -- But the longer example above just shows how one might match on types in
    -- more elaborate scenarios.

  have G_ncard_ge_sum : V(min_comp).ncard + V(other_comp).ncard ≤ V(G).ncard := by
    have : V(min_comp).ncard + V(other_comp).ncard = (V(min_comp) ∪ V(other_comp)).ncard := by
      exact Eq.symm
        (ncard_union_eq disjoint_vx_sets min_comp_finite_vertexSet other_comp_finite_vertexSet)
    rw [this]; clear this
    refine ncard_le_ncard ?_ ?_ <;> assumption

  -- so |min_comp| ≤ n/2
  replace G_ncard_ge_sum : 2 * V(min_comp).ncard ≤ V(G).ncard := by
    linarith

  -- some manipulations left over
  have hle : V(min_comp).ncard ≤ G.minDegree := by linarith
  have hle2 : G.minDegree ≤ min_comp.minDegree := by
    apply minDegree_le_minDegree_of_isCompOf
    rw [←mem_components_iff_isCompOf]
    exact min_comp_spec.1
  replace hle : V(min_comp).ncard ≤ min_comp.minDegree := by linarith
  have hlt : min_comp.minDegree < V(min_comp).ncard := by
    have min_comp_simple : min_comp.Simple := sorry
    refine minDegree_lt_vertexCount ?_ ?_
    · exact Finite.mono hFinite min_comp_spec.1.le
    · rw [NeBot_iff_vertexSet_nonempty]
      exact min_comp_spec.1.nonempty

  linarith

def pathSet (G : Graph α β) := {p | IsPath G p}

lemma pathSet_finite (G : Graph α β) [G.Simple] (hFinite : G.Finite) :
    G.pathSet.Finite := by
  sorry

lemma pathSet_nonempty (G : Graph α β) (hNeBot : G.NeBot) :
    G.pathSet.Nonempty := by
  sorry

def IsLongestPath (G : Graph α β) (p : WList (α) β) :=
  MaximalFor (· ∈ G.pathSet) (fun w => w.length) p

@[simp]
lemma IsLongestPath.isPath {p} (h : G.IsLongestPath p) : G.IsPath p := h.1

lemma exists_longest_path
    (G : Graph α β) [G.Simple] (hFinite : G.Finite) (hNeBot : G.NeBot) :
    ∃ p, G.IsLongestPath p :=
  Set.Finite.exists_maximalFor _ _ (G.pathSet_finite hFinite) (G.pathSet_nonempty hNeBot)

-- by maximality, each neighbour of is on the path
lemma first_neighbors_mem_path
    (G : Graph α β)
    {P : WList (α) β} (hP : G.IsLongestPath P)
    (x : α) (hx : G.Adj x P.first) :
    x ∈ P := by
  -- suppose not.
  -- then, we will try constructing a longer path by prepending this neighbour
  by_contra! hyp
  obtain ⟨e, he⟩ := hx
  generalize Q_def : cons x e P = Q
  symm at Q_def
  have hQ : G.IsPath Q := by simp_all
  have hQ_len : Q.length = P.length + 1 := by simp_all
  have hQ_path : Q ∈ G.pathSet := hQ
  have maximality := maximalFor_is_upper_bound _ hP _ hQ_path
  linarith

-- similarly, the same statement but reverse in direction
lemma last_neighbors_mem_path
    (G : Graph α β)
    {P : WList (α) β} (hP : G.IsLongestPath P)
    (x : α) (hx : G.Adj x P.last) :
    x ∈ P := by
  sorry

-- cycles in simple graphs are nontrivial
lemma IsCycle.nontrivial_of_simple
    [G.Simple]
    {P} (hP : G.IsCycle P) : P.Nontrivial := by
  obtain (h|h) := hP.loop_or_nontrivial
  swap; assumption
  exfalso
  obtain ⟨x,e,rfl⟩ := h
  replace hP := hP.isTrail
  rw [cons_isTrail_iff] at hP
  apply hP.2.1.ne; simp

-- cycles in simple graphs are of length at least 3
lemma IsCycle.cycle_length_ge_3_of_simple
    [G.Simple]
    {P} (hP : G.IsCycle P) :
    3 ≤ P.length := by
  by_contra! hyp_contra
  replace hyp_contra : P.length = 2 := by
    suffices 2 ≤ P.length by linarith
    have P_nontrivial := hP.nontrivial_of_simple
    linarith [P_nontrivial.one_lt_length]
  rw [hP.length_eq_two_iff] at hyp_contra
  obtain ⟨x,y,e,f,_, hne, rfl⟩ := hyp_contra
  have h_e_link : G.IsLink e x y := by
    replace hP := hP.isTrail
    simp_all
  have h_f_link : G.IsLink f y x := by
    replace hP := hP.isTrail
    simp_all
  symm at h_f_link
  apply hne
  have := IsLink.unique_edge h_e_link h_f_link
  assumption
