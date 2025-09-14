import Matroid.Graph.Subgraph.Delete
import Matroid.ForMathlib.Partition.Lattice

variable {α β ι ι' : Type*} {x y z u v w : Set α} {e f : β} {G G₁ G₂ H H₁ H₂ : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set (Set α)} {s t : Set (Graph α β)} {P Q : Partition (Set α)}

open Set Function

/- For Mathlib -/

@[simp]
lemma Option.elim_eq_const_of_isEmpty {α : Type*} [hα : IsEmpty α] (f : α → β) (b : β) :
    (Option.elim · b f) = fun _ ↦ b :=
  funext fun a ↦ match a with
  | none => rfl
  | some a => hα.elim a

open scoped Sym2 Graph

namespace Graph


/-! ### Strongly disjointness -/

/-- Two graphs are strongly disjoint if their edge sets and vertex sets are disjoint.
    This is a stronger notion of disjointness than `Disjoint`,
    see `disjoint_iff_vertexSet_disjoint`. -/
@[mk_iff]
structure StronglyDisjoint (G H : Graph α β) : Prop where
  vertex : Disjoint V(G) V(H)
  edge : Disjoint E(G) E(H)

lemma StronglyDisjoint.symm (h : G.StronglyDisjoint H) : H.StronglyDisjoint G :=
  ⟨h.1.symm, h.2.symm⟩

lemma StronglyDisjoint_iff_of_le_le (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) :
    StronglyDisjoint H₁ H₂ ↔ Disjoint V(H₁) V(H₂) := by
  refine ⟨StronglyDisjoint.vertex, fun h ↦ ⟨h, disjoint_left.2 fun e he₁ he₂ ↦ ?_⟩⟩
  obtain ⟨x, y, he₁⟩ := exists_isLink_of_mem_edgeSet he₁
  exact h.notMem_of_mem_left he₁.left_mem ((he₁.of_le h₁).of_le_of_mem h₂ he₂).left_mem

lemma StronglyDisjoint.disjoint (h : G.StronglyDisjoint H) : Disjoint G H := by
  rintro H' hH'G hH'H
  rw [le_bot_iff, ← vertexSet_eq_empty_iff]
  have := le_inf (vertexSet_mono hH'G) <| vertexSet_mono hH'H
  rwa [h.vertex.eq_bot, le_bot_iff] at this

/-! ### Compatibility -/

def CompatibleAt (e : β) (G H : Graph α β) : Prop := e ∈ E(G) → e ∈ E(H) → G.IsLink e = H.IsLink e

lemma compatibleAt_def :
    CompatibleAt e G H ↔ (e ∈ E(G) → e ∈ E(H) → ∀ x y, G.IsLink e x y ↔ H.IsLink e x y) := by
  simp [CompatibleAt, funext_iff]

lemma CompatibleAt.symm (h : CompatibleAt e G H) : CompatibleAt e H G :=
  fun he1 he2 ↦ (h he2 he1).symm

lemma CompatibleAt.comm : CompatibleAt e G H ↔ CompatibleAt e H G :=
  ⟨CompatibleAt.symm, CompatibleAt.symm⟩

lemma compatibleAt_self : CompatibleAt e G G := fun _ _ ↦ rfl

instance {e : β} : IsRefl (Graph α β) (CompatibleAt e) := ⟨fun _ _ _ ↦ rfl⟩

instance {e : β} : IsSymm (Graph α β) (CompatibleAt e) := ⟨fun _ _ ↦ CompatibleAt.symm⟩

-- This is not transitive.

lemma compatibleAt_symmetric : Symmetric (CompatibleAt e (α := α)) := fun _ _ ↦ CompatibleAt.symm

lemma CompatibleAt.isLink_iff (h : CompatibleAt e G H) (heG : e ∈ E(G)) (heH : e ∈ E(H)) :
    G.IsLink e x y ↔ H.IsLink e x y := by
  rw [h heG heH]

lemma compatibleAt_of_notMem_left (he : e ∉ E(G)) : CompatibleAt e G H := by
  simp [CompatibleAt, he]

lemma compatibleAt_of_notMem_right (he : e ∉ E(H)) : CompatibleAt e G H := by
  simp [CompatibleAt, he]

lemma IsLink.compatibleAt_iff_left (hIsLink : G.IsLink e x y) :
    CompatibleAt e G H ↔ (e ∈ E(H) → H.IsLink e x y) :=
  ⟨fun h heH ↦ by rwa [← CompatibleAt.isLink_iff h hIsLink.edge_mem heH], fun h heG heH ↦
  (isLink_eq_isLink_iff_exists_isLink_of_mem_edgeSet heG).mpr ⟨x, y, hIsLink, h heH⟩⟩

lemma IsLink.compatibleAt_iff_right (h : H.IsLink e x y) :
    CompatibleAt e G H ↔ (e ∈ E(G) → G.IsLink e x y) := by
  rw [CompatibleAt.comm]
  exact compatibleAt_iff_left h

lemma IsLink.of_compatibleAt (he : G.IsLink e x y) (h : CompatibleAt e G H) (heH : e ∈ E(H)) :
    H.IsLink e x y := (he.compatibleAt_iff_left).mp h heH

lemma CompatibleAt.mono_left {G₀ : Graph α β} (h : CompatibleAt e G H) (hle : G₀ ≤ G) :
    CompatibleAt e G₀ H :=
  compatibleAt_def.2 fun heG₀ heH _ _ ↦ ⟨fun h' ↦ (h'.of_le hle).of_compatibleAt h heH,
    fun h' ↦ (h'.of_compatibleAt h.symm (edgeSet_mono hle heG₀)).of_le_of_mem hle heG₀⟩

lemma CompatibleAt.mono_right {H₀ : Graph α β} (h : CompatibleAt e G H) (hH₀ : H₀ ≤ H) :
    CompatibleAt e G H₀ :=
  (h.symm.mono_left hH₀).symm

lemma CompatibleAt.mono {G₀ H₀ : Graph α β} (h : CompatibleAt e G H) (hG : G₀ ≤ G) (hH : H₀ ≤ H) :
    CompatibleAt e G₀ H₀ :=
  (h.mono_left hG).mono_right hH

lemma CompatibleAt.induce_left (h : CompatibleAt e G H) (P : Partition (Set α)) :
    CompatibleAt e G[P] H := by
  rintro ⟨x, y, ⟨he, hx, hy⟩⟩ heH
  ext z w
  rw [← h he.edge_mem heH, induce_isLink_iff, he.isLink_iff]
  aesop

lemma CompatibleAt.induce_right (h : CompatibleAt e G H) (P : Partition (Set α)) :
    CompatibleAt e G H[P] :=
  (h.symm.induce_left P).symm

lemma CompatibleAt.induce (h : CompatibleAt e G H) {P : Partition (Set α)} :
    CompatibleAt e G[P] H[P] :=
  (h.induce_left P).induce_right P

/-- Two graphs are `Compatible` if the edges in their intersection agree on their ends -/
def Compatible (G H : Graph α β) : Prop := EqOn G.IsLink H.IsLink (E(G) ∩ E(H))

lemma Compatible.isLink_eq (h : G.Compatible H) (heG : e ∈ E(G)) (heH : e ∈ E(H)) :
    G.IsLink e = H.IsLink e :=
  h ⟨heG, heH⟩

lemma Compatible.symm (h : G.Compatible H) : H.Compatible G := by
  rwa [Compatible, inter_comm, eqOn_comm]

instance : IsSymm (Graph α β) Compatible where
  symm _ _ := Compatible.symm

@[simp]
lemma compatible_symmetric : Symmetric (@Compatible α β) :=
  fun _ _ ↦ Compatible.symm

lemma compatible_comm : G.Compatible H ↔ H.Compatible G :=
  ⟨Compatible.symm, Compatible.symm⟩

/-- Two subgraphs of the same graph are compatible. -/
lemma compatible_of_le_le {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) : H₁.Compatible H₂ :=
  ((isLink_eqOn_of_le h₁).mono inter_subset_left).trans <|
    (isLink_eqOn_of_le h₂).symm.mono inter_subset_right

lemma compatible_of_le (h : H ≤ G) : H.Compatible G := compatible_of_le_le h le_rfl

lemma IsLink.of_compatible (h : G.IsLink e x y) (hGH : G.Compatible H) (heH : e ∈ E(H)) :
    H.IsLink e x y := by
  rwa [← hGH ⟨h.edge_mem, heH⟩]

lemma Inc.of_compatible (h : G.Inc e x) (hGH : G.Compatible H) (heH : e ∈ E(H)) :
    H.Inc e x := by
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy.of_compatible hGH heH⟩

@[simp]
lemma compatible_self (G : Graph α β) : G.Compatible G :=
  eqOn_refl ..

instance : IsRefl (Graph α β) Compatible where
  refl G := G.compatible_self

lemma Compatible.of_disjoint_edgeSet (h : Disjoint E(G) E(H)) : Compatible G H := by
  simp [Compatible, h.inter_eq]

@[simp]
lemma compatible_edgeDelete_right : G.Compatible (H ＼ E(G)) :=
  Compatible.of_disjoint_edgeSet disjoint_sdiff_right

/-- Used to simplify the definition of the union of a pair. -/
@[simp]
lemma pairwise_compatible_edgeDelete : ({G, H ＼ E(G)} : Set (Graph α β)).Pairwise Compatible := by
  simp [pairwise_iff_of_refl, compatible_edgeDelete_right.symm]

lemma Compatible.mono_left {G₀ : Graph α β} (h : Compatible G H) (hG₀ : G₀ ≤ G) :
    Compatible G₀ H :=
  ((isLink_eqOn_of_le hG₀).mono inter_subset_left).trans
    (h.mono (inter_subset_inter_left _ (edgeSet_mono hG₀)))

lemma Compatible.mono_right {H₀ : Graph α β} (h : Compatible G H) (hH₀ : H₀ ≤ H) :
    Compatible G H₀ :=
  (h.symm.mono_left hH₀).symm

lemma Compatible.mono {G₀ H₀ : Graph α β} (h : G.Compatible H) (hG : G₀ ≤ G) (hH : H₀ ≤ H) :
    G₀.Compatible H₀ :=
  (h.mono_left hG).mono_right hH

lemma Compatible.induce_left (h : Compatible G H) (P : Partition (Set α)) : G[P].Compatible H := by
  intro e ⟨heG, heX⟩
  ext x y
  obtain ⟨u, v, heuv : G.IsLink e u v, hu, hv⟩ := heG
  simp only [induce_isLink_iff, ← h ⟨heuv.edge_mem, heX⟩, and_iff_left_iff_imp]
  intro h
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h.eq_and_eq_or_eq_and_eq heuv <;> simp_all

lemma Compatible.induce_right (h : Compatible G H) (P : Partition (Set α)) :
    G.Compatible H[P] :=
  (h.symm.induce_left P).symm

lemma Compatible.induce (h : Compatible G H) : G[P].Compatible H[P] :=
  (h.induce_left P).induce_right P

lemma Compatible.vertexDelete (h : Compatible G H) : (G - X).Compatible (H - X) :=
  h.mono vertexDelete_le vertexDelete_le

lemma Compatible.edgeDelete (h : Compatible G H) : (G ＼ F).Compatible (H ＼ F) :=
  h.mono edgeDelete_le edgeDelete_le

lemma Compatible.edgeRestrict (h : Compatible G H) : (G ↾ F).Compatible (H ↾ F) :=
  h.mono edgeRestrict_le edgeRestrict_le

@[simp]
lemma Compatible.induce_induce : G[P].Compatible G[Q] :=
  Compatible.induce_left (Compatible.induce_right G.compatible_self _) _

lemma Compatible.stronglyDisjoint_of_vertexSet_disjoint (h : G.Compatible H)
    (hV : Disjoint V(G) V(H)) : G.StronglyDisjoint H := by
  refine ⟨hV, disjoint_left.2 fun e he he' ↦ ?_⟩
  obtain ⟨x, y, hexy⟩ := exists_isLink_of_mem_edgeSet he
  exact hV.notMem_of_mem_left hexy.left_mem (h ⟨he, he'⟩ ▸ hexy).left_mem

lemma Compatible.disjoint_iff_vertexSet_disjoint (h : G.Compatible H) :
    G.StronglyDisjoint H ↔ Disjoint V(G) V(H) :=
  ⟨(·.vertex), h.stronglyDisjoint_of_vertexSet_disjoint⟩

lemma StronglyDisjoint.compatible (h : G.StronglyDisjoint H) : G.Compatible H :=
  Compatible.of_disjoint_edgeSet h.edge

lemma Compatible.edgeSet_disjoint_of_vertexSet_disjoint (h : G.Compatible H)
    (hV : Disjoint V(G) V(H)) : Disjoint E(G) E(H) := by
  by_contra he
  obtain ⟨e, heG, heH⟩ := not_disjoint_iff.mp he
  obtain ⟨x, y, hexy⟩ := exists_isLink_of_mem_edgeSet heG
  exact hV.notMem_of_mem_left hexy.left_mem <| hexy.of_compatible h heH |>.left_mem

lemma stronglyDisjoint_iff_vertexSet_disjoint_compatible :
    G.StronglyDisjoint H ↔ Disjoint V(G) V(H) ∧ G.Compatible H :=
  ⟨fun h => ⟨h.vertex, h.compatible⟩,
    fun ⟨hdisj, hco⟩ => ⟨hdisj, hco.edgeSet_disjoint_of_vertexSet_disjoint hdisj⟩⟩

@[deprecated "Pairwise.const_of_refl" (since := "2025-07-30")]
lemma pairwise_compatible_const (G : Graph α β) : Pairwise (Compatible on fun (_ : ι) ↦ G) := by
  simp [Pairwise]

@[deprecated "Pairwise.onFun_comp_of_refl" (since := "2025-07-30")]
lemma pairwise_compatible_comp {ι ι' : Type*} {G : ι → Graph α β} (hG : Pairwise (Compatible on G))
    (f : ι' → ι): Pairwise (Compatible on (G ∘ f)) := by
  rw [onFun_comp]
  exact Pairwise.onFun_of_refl hG _

/-- useful with `Pairwise` and `Set.Pairwise`.-/
@[simp]
lemma stronglyDisjoint_le_compatible : @StronglyDisjoint α β ≤ Compatible :=
  fun _ _ ↦ StronglyDisjoint.compatible

end Graph
