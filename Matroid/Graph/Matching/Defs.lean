import Matroid.Graph.Degree.Max
import Matroid.Graph.Bipartite
import Matroid.Parallel

namespace Graph

variable {α β : Type*} {G H C : Graph α β} {S X Y : Set α} {M M' : Set β} {u v x y z : α} {e f : β}

open Set symmDiff WList

/-! ### Matching -/

/-- A matching is a set of edges where no two edges share a vertex.
  Note: This does not exclude loops. Consider assuming `[Loopless G]` to exclude loops. -/
@[mk_iff]
structure IsMatching (G : Graph α β) (M : Set β) : Prop where
  subset : M ⊆ E(G)
  disjoint : ∀ ⦃e f⦄, e ∈ M → f ∈ M → e ≠ f → Disjoint V(G, e) V(G, f)

@[mk_iff]
structure IsMaxMatching (G : Graph α β) (M : Set β) : Prop extends G.IsMatching M where
  max : ∀ M', G.IsMatching M' → M'.encard ≤ M.encard
attribute [grind .] IsMatching.subset IsMatching.disjoint IsMaxMatching.max

noncomputable def matchingNumber (G : Graph α β) : ℕ∞ :=
  sSup {n | ∃ M, G.IsMatching M ∧ n = M.encard}

scoped notation "ν(" G ")" => matchingNumber G

def IsMatchable (G : Graph α β) (S : Set α) : Prop := ∃ M, G.IsMatching M ∧ V(G, M) = S

def matchingNumberSet (G : Graph α β) : Set ℕ∞ :=
  {n | ∃ M, G.IsMatching M ∧ n = M.encard}

@[simp, grind =]
lemma matchingNumberSet_eq : G.matchingNumberSet = {n | ∃ M, G.IsMatching M ∧ n = M.encard} := rfl

@[simp, grind .]
lemma IsMatching.encard_mem_matchingNumberSet (hM : G.IsMatching M) :
    M.encard ∈ G.matchingNumberSet :=
  ⟨M, hM, rfl⟩

lemma IsMatching.encard_le (hM : G.IsMatching M) : M.encard ≤ ν(G) := by
  unfold matchingNumber
  refine le_sSup ?_
  refine ⟨M, hM, rfl⟩

lemma le_matchingNumber_of_mem_matchingNumberSet {n} (hn : n ∈ G.matchingNumberSet) : n ≤ ν(G) := by
  obtain ⟨M, hM, rfl⟩ := hn
  exact hM.encard_le

lemma IsMaxMatching.encard (h : G.IsMaxMatching M) : M.encard = ν(G) := by
  unfold matchingNumber
  symm
  refine IsGreatest.csSup_eq ?_
  refine ⟨h.encard_mem_matchingNumberSet, ?_⟩
  simp [upperBounds]
  grind only [max]

lemma IsMatching.isMaxMatching_of_encard_eq (hM : G.IsMatching M) (h : M.encard = ν(G)) :
    G.IsMaxMatching M where
  toIsMatching := hM
  max M' hM' := by
    rw [h]
    exact hM'.encard_le

lemma IsMatching.subsingleton_inc (h : G.IsMatching M) (v : α) : (M ∩ E(G, v)).Subsingleton := by
  intro e he f hf
  by_contra hne
  exact (h.disjoint he.1 hf.1 hne).le_bot ⟨he.2, hf.2⟩

lemma IsMatching.degree_le_one (h : G.IsMatching M) (v : α) : (M ∩ E(G, v)).encard ≤ 1 := by
  rw [encard_le_one_iff_subsingleton]
  exact h.subsingleton_inc v

lemma IsMatching.maxDegree_le_one [G.Loopless] (h : G.IsMatching M) : (G ↾ M).MaxDegreeLE 1 := by
  have : ∀ v : α, E(G ↾ M, v).encard ≤ ↑1 := by
    intro v
    refine (encard_le_encard ?_).trans (h.degree_le_one v)
    rintro e ⟨w, hw⟩
    exact ⟨hw.1, w, hw.2⟩
  rw [maxDegreeLE_iff']
  intro v hv
  rw [eDegree_eq_encard_inc]
  exact this v

-- I just realized the next 4ish lemmas are duplicates from `Matching/Def.lean`
@[simp, grind .]
lemma IsMatching.incEdges_subsingleton (hM : G.IsMatching M) (x : α) :
    E(G ↾ M, x).Subsingleton := by
  rw [incEdges_edgeRestrict]
  intro e he f hf
  by_contra! hcon
  have disj := hM.disjoint he.2 hf.2 hcon
  rw [Set.disjoint_left] at disj
  have hxe : x ∈ V(G, e) := by grind
  have hxf : x ∈ V(G, f) := by grind
  exact disj hxe hxf

@[simp, grind .]
lemma IsMatching.incEdges_encard_le_one (hM : G.IsMatching M) (x : α) :
    E(G ↾ M, x).encard ≤ 1 := by
  rw [Set.encard_le_one_iff_subsingleton]
  exact hM.incEdges_subsingleton x

@[simp, grind .]
lemma IsMatching.eDegree_le_one [G.Loopless] (hM : G.IsMatching M) (x : α) :
    (G ↾ M).eDegree x ≤ 1 := by
  rw [eDegree_eq_encard_inc]
  exact hM.incEdges_encard_le_one x

@[simp, grind .]
lemma IsMatching.maxDegreeLE_one [G.Loopless] (hM : G.IsMatching M) : (G ↾ M).MaxDegreeLE 1 :=
  fun x ↦ hM.eDegree_le_one x

@[simp, grind .]
lemma isMatching_empty : G.IsMatching ∅ := by
  constructor <;> simp

@[simp, grind .]
lemma isMatching_singleton (he : e ∈ E(G)) : G.IsMatching {e} := by
  constructor <;> [simpa ; simp]


lemma IsMatching.of_le (hle : G ≤ H) (h : G.IsMatching M) : H.IsMatching M where
  subset := h.subset.trans (edgeSet_mono hle)
  disjoint e f heM hfM hne := by
    unfold endSet
    -- TODO: how to repeat a tactic exactly n times?
    repeat rw [← inc_eq_of_le hle (h.subset ‹_›)]
    exact h.disjoint heM hfM hne

@[simp, grind .]
lemma IsMatching.anti_left (hM : G.IsMatching M) (hle : H ≤ G) (hMH : M ⊆ E(H)) :
    H.IsMatching M := by
  refine ⟨hMH, ?_⟩
  rintro e f heM hfM hne
  refine disjoint_of_subset ?_ ?_ (hM.disjoint heM hfM hne)
  all_goals exact endSet_mono hle _

@[simp, grind .]
lemma IsMatching.anti_right (hM : G.IsMatching M) (h : M' ⊆ M) : G.IsMatching M' := by
  refine ⟨have := hM.subset; by grind, ?_⟩
  intro e f heM' hfM' hne
  exact hM.disjoint (h heM') (h hfM') hne

/-- The restriction of a matching to a subgraph remains a matching. -/
@[simp, grind .]
lemma IsMatching.anti_left' (hM : G.IsMatching M) (hle : H ≤ G) :
    H.IsMatching (E(H) ∩ M) := by
  refine IsMatching.anti_left ?_ hle ?_
  · exact hM.anti_right (by grind)
  grind

lemma isMatching_iff_edgeRestrict_isMatching :
    G.IsMatching M ↔ (G ↾ M).IsMatching M := by
  refine ⟨?_, ?_⟩
  · intro hM
    refine hM.anti_left edgeRestrict_le ?_
    simp only [edgeRestrict_edgeSet, subset_inter_iff, subset_refl, and_true]
    grind only [hM.subset]
  intro hM
  refine hM.of_le edgeRestrict_le

lemma isMaxMatching_iff_maximalFor : G.IsMaxMatching M ↔ MaximalFor G.IsMatching Set.encard M :=
  ⟨fun h => ⟨h.toIsMatching, fun T hT _ ↦ h.2 T hT⟩,
    fun h => ⟨h.1, fun T hT ↦ (le_total T.encard M.encard).elim id <| h.2 hT⟩⟩

lemma matchingNumber_mono (hle : G ≤ H) : ν(G) ≤ ν(H) := by
  -- any matching of G can be lifted to a matching of H
  conv => lhs; unfold matchingNumber
  rw [sSup_le_iff]
  rintro _ ⟨M, hM, rfl⟩
  exact hM.of_le hle |>.encard_le

-- If every vertex has at most 1 incident edge, then it must be a matching.
lemma isMatching_of_encard_incEdges_le_one
    (M : Set β)
    (hM_subset : M ⊆ E(G))
    (h : ∀ x ∈ V(G), E(G ↾ M, x).encard ≤ 1) :
    G.IsMatching M where
  subset := hM_subset
  disjoint e f he hf hne := by
    by_contra! hcon
    rw [not_disjoint_iff_nonempty_inter] at hcon
    obtain ⟨x, hxe, hxf⟩ := hcon
    simp at hxe hxf
    have hxP : x ∈ G.vertexSet := hxe.vertex_mem
    simp only [incEdges_edgeRestrict, Set.encard_le_one_iff_subsingleton] at h
    specialize h _ hxP ⟨hxe, he⟩ ⟨hxf, hf⟩
    contradiction

lemma isMatching_of_eDegree_le_one
    (M : Set β)
    (hM_subset : M ⊆ E(G))
    (h : ∀ x ∈ V(G), (G ↾ M).eDegree x ≤ 1) :
    G.IsMatching M where
  subset := hM_subset
  disjoint e f he hf hne := by
    by_contra! hcon
    rw [not_disjoint_iff_nonempty_inter] at hcon
    obtain ⟨x, hxe, hxf⟩ := hcon
    simp at hxe hxf
    have hxP : x ∈ G.vertexSet := hxe.vertex_mem
    replace h : ∀ x ∈ V(G), E(G ↾ M, x).encard ≤ 1 := by
      intro x hx
      grw [encard_setOf_inc_le_eDegree (G ↾ M) x]
      exact h _ hx
    simp only [incEdges_edgeRestrict, Set.encard_le_one_iff_subsingleton] at h
    specialize h _ hxP ⟨hxe, he⟩ ⟨hxf, hf⟩
    contradiction

/-! ### Cover -/

structure IsCover (G : Graph α β) (S : Set α) : Prop where
  subset : S ⊆ V(G)
  cover : E(G) ⊆ E(G, S)


structure IsMinCover (G : Graph α β) (S : Set α) : Prop extends IsCover G S where
  min : ∀ T, IsCover G T → S.encard ≤ T.encard

noncomputable def coverNumber (G : Graph α β) : ℕ∞ :=
  sInf {n | ∃ S, G.IsCover S ∧ n = S.encard}

scoped notation "τ(" G ")" => coverNumber G

def coverNumberSet (G : Graph α β) : Set ℕ∞ :=
  {n | ∃ S, G.IsCover S ∧ n = S.encard}

@[simp]
lemma coverNumberSet_eq : G.coverNumberSet = {n | ∃ S, G.IsCover S ∧ n = S.encard} := rfl


lemma IsCover.mem_or_mem_of_isLink (h : G.IsCover S) (he : G.IsLink e u v) : u ∈ S ∨ v ∈ S := by
  have cover := h.cover
  have e_mem : e ∈ E(G, S) := h.cover he.edge_mem
  rw [mem_setIncEdges_iff] at e_mem
  obtain ⟨x, hxS, hx⟩ := e_mem
  have := hx.eq_or_eq_of_isLink he
  grind

lemma IsCover.le_encard (h : G.IsCover S) : τ(G) ≤ S.encard := by
  unfold coverNumber
  grind [sInf_le]

lemma IsMinCover.encard (h : G.IsMinCover S) : S.encard = τ(G) := by
  unfold coverNumber
  refine le_antisymm ?_ h.le_encard
  have := h.min
  grind [le_sInf]

lemma coverNumber_le_of_mem_coverNumberSet {n} (hn : n ∈ G.coverNumberSet) : τ(G) ≤ n := by
  obtain ⟨S, hS, rfl⟩ := hn
  exact hS.le_encard

-- TODO: rename; unless we decide to drop the subset condition, then this becomes obsolete
lemma IsCover.encard_le_vertexSet_encard (h : G.IsCover S) : S.encard ≤ V(G).encard := by
  exact encard_le_encard h.subset

lemma isMinCover_iff_minimalFor : G.IsMinCover S ↔ MinimalFor G.IsCover Set.encard S :=
  ⟨fun h => ⟨h.toIsCover, fun T hT _ ↦ h.min T hT⟩,
    fun h => ⟨h.1, fun T hT ↦ (le_total T.encard S.encard).elim (h.2 hT) id⟩⟩

lemma IsCover.of_vertexDelete (h : (G - X).IsCover S) : G.IsCover ((V(G) ∩ X) ∪ S) where
  subset := by
    have := h.subset
    simp at this
    tauto_set
  cover e he := by
    rw [edge_mem_iff_exists_isLink] at he
    obtain ⟨x, y, hexy⟩ := he
    simp
    wlog hx : x ∈ X ∨ x ∈ S with aux
    · specialize aux h e y x hexy.symm
      apply aux; clear aux
      simp at hx
      obtain (hy|hy) := em (y ∈ X)
        <;> [left ; right]
      · assumption
      replace hexy : (G - X).IsLink e x y := by
        refine hexy.of_le_of_mem vertexDelete_le ?_
        -- TODO: add grind tags for these simps; in general whenever the pattern
        -- `simp; grind` shows up, add grind tags to those simp lemmas
        simp only [vertexDelete_edgeSet, mem_setOf_eq]; grind
      grind [h.mem_or_mem_of_isLink hexy]
    refine ⟨x, ?_, hexy.inc_left⟩
    have : x ∈ V(G) := hexy.left_mem
    grind


lemma IsCover.isMinCover_of_encard_eq (hS : G.IsCover S) (h : S.encard = τ(G)) :
    G.IsMinCover S where
  toIsCover := hS
  min T hT := by
    grind [coverNumber, sInf_le]

/-- There exists a trivial cover (the entire vertex set). -/
lemma isCover_vertexSet (G : Graph α β) : G.IsCover V(G) where
  subset := by rfl
  cover e he := by
    simpa only [setIncEdges_vertexSet]

-- Might be useful to have it in `Exists` form
lemma exists_isCover (G : Graph α β) : ∃ S, G.IsCover S := ⟨V(G), G.isCover_vertexSet⟩

lemma vertexSet_encard_mem_coverNumberSet : V(G).encard ∈ G.coverNumberSet := by
  simp
  refine ⟨V(G), G.isCover_vertexSet, rfl⟩

lemma coverNumberSet_nonempty : G.coverNumberSet.Nonempty := by
  refine ⟨V(G).encard, vertexSet_encard_mem_coverNumberSet⟩

lemma coverNumber_le_vertexSet_encard (G : Graph α β) : τ(G) ≤ V(G).encard := by
  simp only [coverNumber]
  refine sInf_le_of_le G.vertexSet_encard_mem_coverNumberSet (le_refl _)

-- lemma exists_isMinCover_of_finite [G.Finite] : ∃ S, G.IsMinCover S := by
--   have hle := G.coverNumber_le_vertexSet_encard
--   have finite_encard : V(G).encard ≠ ⊤ := by
--     have := G.vertexSet_finite
--     exact encard_ne_top_iff.mpr this
--   have solver : τ(G) ∈ G.coverNumberSet :=
--     ENat.sInf_mem coverNumberSet_nonempty
--   simp at solver
--   obtain ⟨S, hS, hS_min⟩ := solver
--   refine ⟨S, hS.isMinCover_of_encard_eq hS_min.symm⟩

-- kinda wacky that this always exists...
lemma exists_isMinCover (G : Graph α β) : ∃ S, G.IsMinCover S := by
  have : τ(G) ∈ G.coverNumberSet := csInf_mem coverNumberSet_nonempty
  simp at this
  obtain ⟨S, hS, hS_min⟩ := this
  refine ⟨S, hS.isMinCover_of_encard_eq hS_min.symm⟩

lemma IsCover.intersect_endSet_nonempty (hS : G.IsCover S) (he : e ∈ E(G)) :
    Nonempty ↑(S ∩ V(G, e)) := by
  have ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  obtain (h|h) := hS.mem_or_mem_of_isLink hxy
    <;> [refine ⟨x, ?_⟩ ; refine ⟨y, ?_⟩]
    <;> tauto_set

noncomputable def IsMatching.mapToCover (hM : G.IsMatching M) (hS : G.IsCover S) : M → S := by
  -- we should be able to arbitrarily choose either vertex for any e ∈ M
  intro ⟨e, he⟩
  have heE : e ∈ E(G) := hM.subset he
  -- take ends, cap with S?
  have nonempty := hS.intersect_endSet_nonempty heE
  obtain ⟨x, hx⟩ := Classical.choice nonempty
  refine ⟨x, hx.1⟩

-- set_option pp.proofs true in
lemma IsMatching.mapToCover_inj (hM : G.IsMatching M) (hS : G.IsCover S) :
    Function.Injective (hM.mapToCover hS) := by
  intro ⟨e, he⟩ ⟨f, hf⟩ heq
  simp only [Subtype.mk.injEq]
  by_contra! hcon
  unfold mapToCover at heq
  simp at heq
  -- TODO: this still feels suboptimal.
  generalize_proofs ex ey at heq
  -- this leaves `heq : ↑(Classical.choice ex) = ↑(Classical.choice ey)`
  -- directly trying to destruct ex/ey with `obtain` messes things up
  -- (it effectively undoes the `generalize_proofs`)
  set x := Classical.choice ex
  set y := Classical.choice ey
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  simp only at heq
  have disj := hM.disjoint he hf hcon
  refine disj.notMem_of_mem_left (a := x) hx.2 ?_
  rw [heq]
  exact hy.2

-- set_option pp.proofs true in
lemma IsMatching.mapToCover_inc (hM : G.IsMatching M) (hS : G.IsCover S) (he : e ∈ M) :
    G.Inc e (hM.mapToCover hS ⟨e, he⟩) := by
  simp only [mapToCover]
  set x := (Classical.choice (IsCover.intersect_endSet_nonempty hS (hM.subset he)))
  have hxE : ↑x ∈ V(G, e) := x.2.2
  rwa [← mem_endSet_iff]

lemma matchingNumber_le_coverNumber : ν(G) ≤ τ(G) := by
  simp only [matchingNumber, coverNumber]
  simp only [le_sInf_iff, sSup_le_iff]
  rintro t ⟨C, hS, rfl⟩ n ⟨M, hM, rfl⟩
  have solver := (hM.mapToCover_inj hS).encard_range
  simp only [ENat.card_coe_set_eq, range] at solver
  refine le_trans solver ?_
  rw [show C.encard = (univ : Set ↑C).encard by simp]
  refine encard_le_encard (by grind)

lemma exists_isMaxMatching' (G : Graph α β) (hν : ν(G) ≠ ⊤) : ∃ M, G.IsMaxMatching M := by
  have : ν(G) ∈ G.matchingNumberSet := by
    have injOn : InjOn ENat.toNat G.matchingNumberSet := by
      intro i hi j hj heq
      have hi_le : i ≤ ν(G) := le_matchingNumber_of_mem_matchingNumberSet hi
      have hj_le : j ≤ ν(G) := le_matchingNumber_of_mem_matchingNumberSet hj
      enat_to_nat!
      simp at heq
      assumption
    have im_eq : ENat.toNat '' G.matchingNumberSet ⊆ {i | i ≤ ν(G).toNat} := by
      intro i hi
      obtain ⟨n, hn, rfl⟩ := hi
      obtain ⟨M, hM, rfl⟩ := hn
      exact ENat.toNat_le_toNat hM.encard_le hν
    have finite : G.matchingNumberSet.Finite := by
      refine Set.Finite.of_finite_image ?_ injOn
      refine Set.Finite.subset (finite_le_nat ν(G).toNat) im_eq
    have : G.matchingNumberSet.Nonempty :=
      ⟨0, ∅, isMatching_empty, encard_empty.symm⟩
    exact this.csSup_mem finite
  obtain ⟨M, hM, hM_eq⟩ := this
  refine ⟨M, hM.isMaxMatching_of_encard_eq hM_eq.symm⟩

lemma exists_isMaxMatching (G : Graph α β) [G.Finite] : ∃ M, G.IsMaxMatching M := by
  refine G.exists_isMaxMatching' ?_
  have := G.matchingNumber_le_coverNumber
  have τ_finite : τ(G) < ⊤ := by
        have : V(G).encard < ⊤ := encard_lt_top_iff.mpr ‹G.Finite›.vertexSet_finite
        have := G.coverNumber_le_vertexSet_encard
        enat_to_nat!
  enat_to_nat!

lemma IsMatching.encard_le_isCover_encard (hM : G.IsMatching M) (hS : G.IsCover S) :
    M.encard ≤ S.encard := by
  grw [hM.encard_le, ← hS.le_encard]
  exact matchingNumber_le_coverNumber

lemma IsMatching.mapToCover_range_eq_of_encard_eq [G.Finite]
    (hS : G.IsCover S) (hM : G.IsMatching M) (h : S.encard = M.encard) :
    range (hM.mapToCover hS) = S := by
  have S_finite : S.Finite :=
    Set.Finite.subset vertexSet_finite hS.subset
  have M_finite : M.Finite :=
    Set.Finite.subset edgeSet_finite hM.subset
  have subset : Subtype.val '' range (hM.mapToCover hS) ⊆ S := by
    simp only [image_subset_iff, Subtype.coe_preimage_self, subset_univ]
    -- TODO: pain point, switching between encard and ncard
    -- (need ncard because `Set.subset_iff_eq_of_ncard_le` has no encard equivalent)
  have : (Subtype.val '' range (hM.mapToCover hS) |>.ncard) = M.ncard := by
    simp only [ncard_image_of_injective _ Subtype.val_injective,
      ncard_range_of_injective (hM.mapToCover_inj hS), Nat.card_coe_set_eq]
  rwa [← subset_iff_eq_of_ncard_le ?_ S_finite]
  simp only [← S_finite.cast_ncard_eq, ← M_finite.cast_ncard_eq, Nat.cast_inj] at h
  rw [this, h]

-- TODO: rename
lemma IsCover.subgraph_cover (hS : H.IsCover S) (hle : G ≤ H) : G.IsCover (S ∩ V(G)) where
  subset := by tauto_set
  cover := by
    intro e he
    simp
    have heH := (edgeSet_mono hle) he
    rw [edge_mem_iff_exists_isLink] at he
    obtain ⟨x, y, hexy⟩ := he
    obtain h := hS.mem_or_mem_of_isLink (hexy.of_le hle)
    wlog hxS : x ∈ S with aux
    · specialize aux hS hle heH y x hexy.symm h.symm (by grind)
      assumption
    refine ⟨x, ⟨hxS, hexy.left_mem⟩, hexy.inc_left⟩

lemma coverNumber_mono (hle : G ≤ H) : τ(G) ≤ τ(H) := by
  have ⟨S_G, hS_G⟩ := G.exists_isMinCover
  have ⟨S_H, hS_H⟩ := H.exists_isMinCover
  have subcover := hS_H.subgraph_cover hle
  have := hS_G.min _ subcover
  grw [← hS_G.encard, this, ← hS_H.encard]
  grind [encard_le_encard]

-- You can take unions of matchings/covers across strongly disjoint graphs
lemma IsCover.union {H₁ H₂ : Graph α β} {S₁ S₂ : Set α}
    (hS₁ : H₁.IsCover S₁) (hS₂ : H₂.IsCover S₂) (hdisj : H₁.StronglyDisjoint H₂) :
    (H₁ ∪ H₂).IsCover (S₁ ∪ S₂) where
  subset := by grind [union_vertexSet, hS₁.subset, hS₂.subset]
  cover := by
    intro e
    simp [hdisj.compatible.union_inc_iff]
    rintro (he|he)
    · apply exists_isLink_of_mem_edgeSet at he
      obtain ⟨x, y, hexy⟩ := he
      obtain (h|h) := hS₁.mem_or_mem_of_isLink hexy
        <;> [use x; use y]
        <;> refine ⟨Or.inl ‹_›, Or.inl ?_⟩
        <;> [exact hexy.inc_left ; exact hexy.inc_right]
    -- not sure how to golf this better
    apply exists_isLink_of_mem_edgeSet at he
    obtain ⟨x, y, hexy⟩ := he
    obtain (h|h) := hS₂.mem_or_mem_of_isLink hexy
      <;> [use x; use y]
      <;> refine ⟨Or.inr ‹_›, Or.inr ?_⟩
      <;> [exact hexy.inc_left ; exact hexy.inc_right]

lemma IsMinCover.union {T : Set α}
    (hS : G.IsMinCover S) (hT : H.IsMinCover T) (hdisj : G.StronglyDisjoint H) :
    (G ∪ H).IsMinCover (S ∪ T) := by
  refine ⟨hS.toIsCover.union hT.toIsCover hdisj, ?_⟩
  intro A hA
  have hAG : G.IsCover (A ∩ V(G)) :=
    hA.subgraph_cover (G.left_le_union H)
  have hAH : H.IsCover (A ∩ V(H)) := by
    have : H ≤ G ∪ H := by grind only [hdisj.compatible.union_comm, Graph.left_le_union]
    exact hA.subgraph_cover this
  have ST_disj : Disjoint S T := by grind [hS.subset, hT.subset, hdisj.vertex]
  rw [encard_union_eq ST_disj]
  have : A = (A ∩ V(G)) ∪ (A ∩ V(H)) := by
    have : V(G ∪ H) = V(G) ∪ V(H) := by exact union_vertexSet G H
    grind [hA.subset]
  rw [this,
    encard_union_eq (show Disjoint (A ∩ V(G)) (A ∩ V(H)) by grind [hdisj.vertex])];
    clear this
  have hle1 := hAG.le_encard
  have hle2 := hAH.le_encard
  rw [hS.encard, hT.encard]
  exact add_le_add hle1 hle2

lemma IsMatching.union
    {H₁ H₂ : Graph α β} {M₁ M₂ : Set β}
    (hM₁ : H₁.IsMatching M₁)
    (hM₂ : H₂.IsMatching M₂)
    (hdisj : StronglyDisjoint H₁ H₂) :
    (H₁ ∪ H₂).IsMatching (M₁ ∪ M₂) where
  -- TODO: grind tags
  subset := by grind [union_edgeSet, hM₁.subset, hM₂.subset]
  disjoint e f he hf hne := by
    have all_left {M : Set β} {H K : Graph α β}
        (hM : H.IsMatching M) (hdisj : H.StronglyDisjoint K) :
        ∀ ⦃e⦄, e ∈ M → V(H ∪ K, e) = V(H, e) := by
      intro e he
      ext x
      simp only [endSet, mem_setOf_eq, hdisj.compatible.union_inc_iff]
      refine ⟨?_, by grind⟩
      rintro (_|h) <;> [assumption ; exfalso]
      replace he : e ∈ E(H) := hM.subset he
      grind [h.edge_mem, hdisj.edge]
    have all_right : ∀ ⦃e⦄, e ∈ M₂ → V(H₁ ∪ H₂, e) = V(H₂, e) := by
      have := all_left hM₂ hdisj.symm
      simpa only [hdisj.compatible.union_comm]
    specialize all_left hM₁ hdisj
    match he, hf with
    | Or.inl he, Or.inl hf
    | Or.inr he, Or.inr hf =>
      simp only [all_left, all_right, he, hf]
      grind only [= disjoint_left, hM₁.disjoint, hM₂.disjoint]
    | Or.inl he, Or.inr hf
    | Or.inr he, Or.inl hf =>
      simp only [all_left, all_right, he, hf]
      grind only [hdisj.vertex, = disjoint_left, = mem_endSet_iff, → Inc.vertex_mem]

lemma IsMaxMatching.union {N : Set β}
    (hM : G.IsMaxMatching M) (hN : H.IsMaxMatching N) (hdisj : G.StronglyDisjoint H) :
    (G ∪ H).IsMaxMatching (M ∪ N) := by
  refine ⟨hM.toIsMatching.union hN.toIsMatching hdisj, ?_⟩
  intro F hF
  have hFG : G.IsMatching (E(G) ∩ F) := hF.anti_left' (G.left_le_union H)
  have hFH : H.IsMatching (E(H) ∩ F) :=
    hF.anti_left' <| by grind only [hdisj.compatible.union_comm, Graph.left_le_union]
  rw [encard_union_eq (show Disjoint M N by grind [hM.subset, hN.subset, hdisj.edge]),
    show F = (E(G) ∩ F) ∪ (E(H) ∩ F) by grind [hF.subset, union_edgeSet],
    encard_union_eq (show Disjoint (E(G) ∩ F) (E(H) ∩ F) by grind [hdisj.edge]),
    hM.encard, hN.encard]
  have hle1 := hFG.encard_le
  have hle2 := hFH.encard_le
  exact add_le_add hle1 hle2

@[simp, grind =]
lemma coverNumber_union (hdisj : G.StronglyDisjoint H) : τ(G ∪ H) = τ(G) + τ(H) := by
  obtain ⟨S, hS⟩ := G.exists_isMinCover
  obtain ⟨T, hT⟩ := H.exists_isMinCover
  have ST_minCover := hS.union hT hdisj
  rw [← hS.encard, ← hT.encard, ← ST_minCover.encard]
  refine encard_union_eq ?_
  grind  [hdisj.vertex, hS.subset, hT.subset]

@[simp, grind =]
lemma matchingNumber_union (hdisj : G.StronglyDisjoint H) : ν(G ∪ H) = ν(G) + ν(H) := by
  obtain (hinf|hfinite) := em' (ν(G) ≠ ⊤ ∧ ν(H) ≠ ⊤)
  · wlog hν : (ν(G) = ⊤) with aux
    · specialize aux hdisj.symm (by grind) (by grind)
      rw [hdisj.compatible.union_comm, aux, add_comm]
    simp [hν]
    rw [matchingNumber, sSup_eq_top] at hν ⊢
    intro b hb
    obtain ⟨n, hn, hbn⟩ := hν b hb
    obtain ⟨M, hM, rfl⟩ := hn
    refine ⟨M.encard, ?_, hbn⟩
    refine ⟨M, hM.of_le (G.left_le_union H), rfl⟩
  obtain ⟨M, hM⟩ := G.exists_isMaxMatching' hfinite.1
  obtain ⟨N, hN⟩ := H.exists_isMaxMatching' hfinite.2
  have MN_maxMatching := hM.union hN hdisj
  rw [← hM.encard, ← hN.encard, ← MN_maxMatching.encard]
  refine encard_union_eq <| by grind [hdisj.edge, hM.subset, hN.subset]



/-! ### restrict₂ (lemmas needed for Tutte-Berge?) -/

def IsMatching.restrict₂ (hM : G.IsMatching M) (hM' : G.IsMatching M') : Graph α β :=
  G ↾ (M ∆ M') |>.loopRemove

instance IsMatching.restrict₂.edgeFinite (hM : G.IsMatching M) (hM' : G.IsMatching M')
    [G.EdgeFinite] : (hM.restrict₂ hM').EdgeFinite := by
  sorry

lemma IsMatching.symmDiff_maxDegree_le_two (hM : G.IsMatching M) (hM' : G.IsMatching M') :
    (hM.restrict₂ hM').MaxDegreeLE 2 := by
  sorry

lemma IsMatching.disjoint_inter_of_isCycle_symmDiff (hM : G.IsMatching M)
    (hM' : G.IsMatching M') (hC : C.IsCycle) (hCG : C ≤ hM.restrict₂ hM') :
    Disjoint (E(C) ∩ M) (E(C) ∩ M') := by
  sorry

lemma IsMatching.inter_encard_eq_of_isCycle_isCompOf_symmDiff (hM : G.IsMatching M)
    (hM' : G.IsMatching M') (hC : C.IsCycle) (hCG : C.IsCompOf (hM.restrict₂ hM')) :
    (E(C) ∩ M).encard = (E(C) ∩ M').encard := by
  sorry

-- lemma IsMatching.exists_isPathGraph_isCompOf_symmDiff (hM : G.IsMatching M)
--     (hM' : G.IsMatching M')
--     (hcd : M.encard < M'.encard) [G.EdgeFinite] :
--     ∃ G' : Graph α β, G'.IsCompOf (hM.restrict₂ hM') ∧ G'.IsPathGraph := by
--   contrapose! hcd
--   have hmax := hM.symmDiff_maxDegree_le_two hM'
--   have hcd' : ∀ (G' : Graph α β), G'.IsCompOf (hM.restrict₂ hM') → G'.IsCycle :=
--     fun G' hG' ↦ hG'.isPathGraph_or_isCycle_of_maxDegreeLE hmax |>.resolve_left
--     <| hcd G' hG'
--   clear hcd hmax
--   sorry -- component partition

lemma IsMatching.isMaxMatching_of_vertex_subset (hM : G.IsMatching M) (hsu : V(G) ⊆ V(G, M)) :
    G.IsMaxMatching M where
  toIsMatching := hM
  max M' hM' := by
    -- TODO: how to prove this easily?

    -- sps |M| < |M'|, for contra
    -- then there must be some e ∈ M' \ M

    by_contra! hlt
    -- TODO: i think this lemma is in the wrong file lol
    have ⟨x, hx⟩ := diff_nonempty_of_encard_lt_encard hlt
    sorry

/-! ### Augmenting paths -/

noncomputable def IsPathGraph.first {P : Graph α β} (hP : P.IsPathGraph) : α :=
  hP.choose.first

noncomputable def IsPathGraph.last {P : Graph α β} (hP : P.IsPathGraph) : α :=
  hP.choose.last

-- probably want some generic "external/internal vxs/edges" for forests
-- external vxs are just leaves
-- internal vxs are non-leaves
-- external edges are edges for which at least one endpoint is a leaf
-- internal edges are edges for which both endpoints are not leaves

@[mk_iff]
structure IsAugPath (G : Graph α β) (hM : G.IsMatching M) (P : Graph α β) : Prop where
  subgraph : P ≤ G
  isPathGraph : P.IsPathGraph
  -- all internal vx of P are matched by M
  -- matches_internal : M ∩ E(P) = E(P) \ {P.firstEdge, P.lastEdg e}

/-! ### Structure of graph from maximal matching -/

def Inessential (G : Graph α β) (x : α) : Prop :=
  ∃ M, G.IsMaxMatching M ∧ x ∉ V(G, M)

structure IsOddCompOf (H G : Graph α β) extends H.IsCompOf G where
  finite : V(H).Finite
  odd : Odd V(H).encard

def oddComponents (G : Graph α β) : Set (Graph α β) :=
  {H | H.IsOddCompOf G}
