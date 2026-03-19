import Matroid.Graph.Degree.Max
import Matroid.Graph.Bipartite
import Matroid.Parallel

namespace Graph

variable {α β : Type*} {G H C P : Graph α β} {S X Y : Set α} {M M' : Set β} {u v x y z : α} {e f : β}

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
lemma IsMatching.eDegree_eq_fn [DecidablePred (· ∈ V(G, M))] [G.Loopless] (hM : G.IsMatching M) :
    (G ↾ M).eDegree = fun x ↦ if x ∈ V(G, M) then 1 else 0 := by
  ext x
  rw [eDegree_eq_encard_inc]
  split_ifs with hx
  · rw [encard_eq_one]
    simp at hx
    obtain ⟨e, he, hex⟩ := hx
    have := exists_eq_singleton_iff_nonempty_subsingleton.mpr ⟨⟨e, ?_⟩, hM.incEdges_subsingleton x⟩
    · exact this
    simp
    exact ⟨hex, he⟩
  contrapose hx
  rw [← ne_eq, encard_ne_zero] at hx
  obtain ⟨e, he⟩ := hx
  simp only [incEdges_edgeRestrict, mem_inter_iff, mem_incEdges_iff] at he
  exact ⟨e, he.2, he.1⟩

lemma IsMatching.eDegree_eq_one [G.Loopless] (hM : G.IsMatching M) (hx : x ∈ V(G, M)) :
    (G ↾ M).eDegree x = 1 := by
  classical
  rw [hM.eDegree_eq_fn]
  simp
  exact hx

@[simp, grind .]
lemma IsMatching.eDegree_le_two (hM : G.IsMatching M) (x : α) :
    (G ↾ M).eDegree x ≤ 2 := by
  rw [eDegree_eq_encard_add_encard]
  have bound := hM.incEdges_encard_le_one x
  rw [incEdges_eq_isLoopAt_union_isNonloopAt] at bound
  rw [encard_union_eq (disjoint_isLoopAt_isNonLoopAt)] at bound
  enat_to_nat!; omega

@[simp, grind .]
lemma IsMatching.maxDegreeLE_two (hM : G.IsMatching M) : (G ↾ M).MaxDegreeLE 2 :=
  hM.eDegree_le_two

@[simp, grind .]
lemma IsMatching.locallyFinite (hM : G.IsMatching M) : (G ↾ M).LocallyFinite :=
  MaxDegreeLE.locallyFinite hM.maxDegreeLE_two

lemma IsMatching.matched_vertexSet_encard_eq [G.Loopless] (hM : G.IsMatching M) :
    V(G, M).encard = 2 * M.encard := by
  classical
  have : M = E(G ↾ M) := by
    ext e; grind [hM.subset]
  conv => rhs; rw [this, ← handshake_eDegree]
  clear this
  rw [hM.eDegree_eq_fn, ← ENat.encard_eq_tsum_ite]

lemma IsMatching.matched_vertexSet_encard_le (hM : G.IsMatching M) :
    V(G, M).encard ≤ 2 * M.encard := by
  classical
  have : M = E(G ↾ M) := by
    ext e; grind [hM.subset]
  conv => rhs; rw [this, ← handshake_eDegree]
  clear this
  have hle : (fun x ↦ if x ∈ V(G, M) then 1 else 0) ≤ (G ↾ M).eDegree := by
    intro x
    simp only
    split_ifs with hx
    · obtain ⟨e, he⟩ := hx
      refine Inc.one_le_eDegree (e := e) ?_
      grind only [edgeRestrict_inc_iff]
    exact zero_le _
  grw [← ENat.tsum_le_tsum hle, ← ENat.encard_eq_tsum_ite]

@[simp, grind .]
lemma isMatching_empty : G.IsMatching ∅ := by
  constructor <;> simp

@[simp, grind .]
lemma isMatching_singleton (he : e ∈ E(G)) : G.IsMatching {e} := by
  constructor <;> [simpa ; simp]


lemma IsMatching.mono_left (hle : G ≤ H) (h : G.IsMatching M) : H.IsMatching M where
  subset := h.subset.trans (edgeSet_mono hle)
  disjoint e f heM hfM hne := by
    unfold endSet
    iterate 2 rw [← inc_eq_of_le hle (h.subset ‹_›)]
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
  refine hM.mono_left edgeRestrict_le

lemma isMaxMatching_iff_maximalFor : G.IsMaxMatching M ↔ MaximalFor G.IsMatching Set.encard M :=
  ⟨fun h => ⟨h.toIsMatching, fun T hT _ ↦ h.2 T hT⟩,
    fun h => ⟨h.1, fun T hT ↦ (le_total T.encard M.encard).elim id <| h.2 hT⟩⟩

lemma matchingNumber_mono (hle : G ≤ H) : ν(G) ≤ ν(H) := by
  -- any matching of G can be lifted to a matching of H
  conv => lhs; unfold matchingNumber
  rw [sSup_le_iff]
  rintro _ ⟨M, hM, rfl⟩
  exact hM.mono_left hle |>.encard_le

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
    refine ⟨M, hM.mono_left (G.left_le_union H), rfl⟩
  obtain ⟨M, hM⟩ := G.exists_isMaxMatching' hfinite.1
  obtain ⟨N, hN⟩ := H.exists_isMaxMatching' hfinite.2
  have MN_maxMatching := hM.union hN hdisj
  rw [← hM.encard, ← hN.encard, ← MN_maxMatching.encard]
  refine encard_union_eq <| by grind [hdisj.edge, hM.subset, hN.subset]

lemma subset_induce_incVertexSet (F : Set β) : E(G) ∩ F ⊆ E(G[V(G, F)]) := by
  rw [← Subgraph.induce_incVertexSet_inter_eq F]
  exact inter_subset_left

@[grind →]
lemma disjoint_of_disjoint_incVertexSet {M N : Set β} (h : Disjoint V(G, M) V(G, N)) :
    Disjoint (E(G) ∩ M) (E(G) ∩ N) := by
  have strong_disj : G[V(G, M)].StronglyDisjoint G[V(G, N)] := by
    rw [stronglyDisjoint_iff_vertexSet_disjoint_compatible]
    exact ⟨h, Compatible.induce_induce⟩
  have disj := strong_disj.edge
  rw [disjoint_left] at disj ⊢
  intro e heM heN
  replace heM : e ∈ E(G[V(G, M)]) := subset_induce_incVertexSet _ heM
  replace heN := subset_induce_incVertexSet _ heN
  exact disj heM heN

lemma IsMatching.union' {N : Set β}
    (hM : G.IsMatching M) (hN : G.IsMatching N) (hdisj : Disjoint V(G, M) V(G, N)) :
    G.IsMatching (M ∪ N) := by
  have strong_disj : G[V(G, M)].StronglyDisjoint G[V(G, N)] := by
    rw [stronglyDisjoint_iff_vertexSet_disjoint_compatible]
    exact ⟨hdisj, Compatible.induce_induce⟩
  have hM' : G[V(G, M)].IsMatching M := by
    refine hM.anti_left (induce_le <| G.incVertexSet_subset M) ?_
    grw [← subset_induce_incVertexSet _]
    grind [hM.subset]
  have hN' : G[V(G, N)].IsMatching N := by
    refine hN.anti_left (induce_le <| G.incVertexSet_subset _) ?_
    grw [← subset_induce_incVertexSet _]
    grind [hN.subset]
  have := hM'.union hN' strong_disj
  refine this.mono_left ?_
  exact Graph.union_le
    (induce_le <| G.incVertexSet_subset _)
    (induce_le <| G.incVertexSet_subset _)

/-- for any vertex matched by a matching, there is a unique edge which covers it --/
lemma IsMatching.existsUnique_covering_edge (hM : G.IsMatching M) (hx : x ∈ V(G, M)) :
    ∃! e ∈ M, G.Inc e x := by
  simp at hx
  obtain ⟨e, heM, hex⟩ := hx
  refine ⟨e, ⟨heM, hex⟩, ?_⟩
  rintro f ⟨hfM, hfx⟩
  have he : e ∈ E(G ↾ M, x) := by grind
  have hf : f ∈ E(G ↾ M, x) := by grind
  exact hM.incEdges_subsingleton _ hf he

noncomputable def IsMatching.covering_edge (hM : G.IsMatching M) : V(G, M) → M := by
  rintro ⟨_, hx⟩
  have ex := hM.existsUnique_covering_edge hx
  exact ⟨ex.choose, ex.choose_spec.1.1⟩

@[simp, grind =>]
lemma IsMatching.covering_edge_inc (hM : G.IsMatching M) (x : V(G, M)) :
    G.Inc (hM.covering_edge x) x := by
  simp [covering_edge]
  generalize_proofs pf
  grind only [pf.choose_spec]

@[simp, grind →]
lemma IsMatching.covering_edge_unique (hM : G.IsMatching M) (heM : e ∈ M) (hex : G.Inc e x) :
    e = hM.covering_edge ⟨x, by grind⟩ := by
  simp [covering_edge]
  generalize_proofs pf
  exact pf.choose_spec.2 _ heM hex

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

-- TODO: move
-- For parity with `Nat.mul_left_cancel`
lemma _root_.ENat.mul_left_cancel {n m k : ℕ∞} (hn : 0 < n) (h_top : n ≠ ⊤) (h : n * m = n * k) :
    m = k := by
  have := ENat.mul_right_strictMono hn.ne.symm h_top |>.injective
  exact this h

-- this is not true for general G;
-- in our definition of `IsMatching`, we allow for loops,
-- which means that the 2 vx graph with 1 edge between them and a loop on each vx
-- is a counterexample to the general statement.
lemma IsMatching.isMaxMatching_of_vertex_subset [G.Loopless]
    (hM : G.IsMatching M) (hsu : V(G) ⊆ V(G, M)) :
    G.IsMaxMatching M where
  toIsMatching := hM
  max M' hM' := by
    -- TODO: these fail on grind
    rw [← ENat.mul_le_mul_left_iff (a := 2) (by simp) (by simp)]
    iterate 2 rw [← matched_vertexSet_encard_eq ‹_›]
    grw [encard_le_encard (G.incVertexSet_subset M')]
    exact encard_le_encard hsu

/-! ### Augmenting paths -/

lemma IsPathGraph.simple (hP : P.IsPathGraph) : P.Simple := by
  obtain ⟨p, hp⟩ := hP
  rw [hp.2]
  exact hp.1.toGraph_simple

noncomputable def IsPathGraph.first (hP : P.IsPathGraph) : α :=
  hP.choose.first

noncomputable def IsPathGraph.last (hP : P.IsPathGraph) : α :=
  hP.choose.last

-- TODO: move
lemma _root_.WList.nonempty_iff_toGraph_edgeSet_nonempty {w : WList α β} :
    w.Nonempty ↔ E(w.toGraph).Nonempty := by
  simp [toGraph_edgeSet, nonempty_iff_exists_edge, ← mem_edgeSet_iff]
  exact Iff.symm nonempty_def

 lemma IsPathGraph.setOf_isLeaf_eq (hP : P.IsPathGraph) (hne : E(P).Nonempty) :
    {x | P.IsLeaf x} = {hP.first, hP.last} := by
  have ⟨hp, heq⟩ := hP.choose_spec
  set p := hP.choose
  change {x | P.IsLeaf x} = {p.first, p.last}
  ext x
  refine ⟨?_, ?_⟩
  · simp
    intro hx
    exact hx.eq_first_or_eq_last_of_mem_path hp
      (by rw [← WList.mem_vertexSet_iff, ← WList.toGraph_vertexSet, ← heq]; exact hx.mem)
  simp
  rw [heq, ← nonempty_iff_toGraph_edgeSet_nonempty] at hne
  rintro (rfl|rfl)
    <;> rw [heq]
  · exact hp.first_isLeaf_toGraph hne
  · exact hp.last_isLeaf_toGraph hne

@[simp, grind =>]
lemma IsPathGraph.isLeaf_iff (hP : P.IsPathGraph) (hne : E(P).Nonempty) :
    P.IsLeaf x ↔ x = hP.first ∨ x = hP.last := by
  change x ∈ {x | P.IsLeaf x} ↔ x = hP.first ∨ x = hP.last
  simp [hP.setOf_isLeaf_eq hne]

@[simp, grind →]
lemma IsPathGraph.isLeaf_first (hP : P.IsPathGraph) (hne : E(P).Nonempty) :
    P.IsLeaf hP.first :=
  hP.isLeaf_iff hne |>.mpr (Or.inl rfl)

@[simp, grind →]
lemma IsPathGraph.isLeaf_last (hP : P.IsPathGraph) (hne : E(P).Nonempty) :
    P.IsLeaf hP.last :=
  hP.isLeaf_iff hne |>.mpr (Or.inr rfl)

noncomputable def IsPathGraph.firstEdge (hP : P.IsPathGraph) (hne : E(P).Nonempty) : β := by
  refine WList.Nonempty.firstEdge hP.choose ?_
  rw [hP.choose_spec.2, ← nonempty_iff_toGraph_edgeSet_nonempty] at hne
  assumption

noncomputable def IsPathGraph.lastEdge (hP : P.IsPathGraph) (hne : E(P).Nonempty) : β := by
  refine WList.Nonempty.lastEdge hP.choose ?_
  rw [hP.choose_spec.2, ← nonempty_iff_toGraph_edgeSet_nonempty] at hne
  assumption

lemma _root_.WList.reverse_inc {w : WList α β} (h : w.Inc e x) : w.reverse.Inc e x := by
  obtain ⟨y, h⟩ := h
  refine ⟨y, ?_⟩
  rwa [isLink_reverse_iff]

lemma _root_.WList.reverse_inc_iff {w : WList α β} : w.reverse.Inc e x ↔ w.Inc e x := by
  refine ⟨?_, reverse_inc⟩
  nth_rewrite 2 [← w.reverse_reverse]
  exact reverse_inc

lemma _root_.WList.Nonempty.inc_firstEdge_first {w : WList α β} (hne : w.Nonempty) :
    w.Inc hne.firstEdge w.first := by
  cases w with simp at hne ⊢

lemma _root_.WList.Nonempty.inc_lastEdge_last {w : WList α β} (hne : w.Nonempty) :
    w.Inc hne.lastEdge w.last := by
  rw [← hne.firstEdge_reverse, ← w.reverse_first, ← reverse_inc_iff]
  exact hne.reverse.inc_firstEdge_first

lemma IsPathGraph.inc_firstEdge_first (hP : P.IsPathGraph) (hne : E(P).Nonempty) :
    P.Inc (hP.firstEdge hne) hP.first := by
  rw [hP.choose_spec.2, ← nonempty_iff_toGraph_edgeSet_nonempty] at hne
  set p := hP.choose
  change P.Inc (hne.firstEdge) p.first
  rw [show P = p.toGraph by exact hP.choose_spec.2, hP.choose_spec.1.isWalk.wellFormed.toGraph_inc]
  exact hne.inc_firstEdge_first

lemma IsPathGraph.inc_lastEdge_last (hP : P.IsPathGraph) (hne : E(P).Nonempty) :
    P.Inc (hP.lastEdge hne) hP.last := by
  rw [hP.choose_spec.2, ← nonempty_iff_toGraph_edgeSet_nonempty] at hne
  set p := hP.choose
  change P.Inc (hne.lastEdge) p.last
  rw [show P = p.toGraph by exact hP.choose_spec.2, hP.choose_spec.1.isWalk.wellFormed.toGraph_inc]
  exact hne.inc_lastEdge_last

lemma IsPathGraph.firstEdge_isLeafEdge (hP : P.IsPathGraph) (hne : E(P).Nonempty) :
    P.IsLeafEdge <| hP.firstEdge hne := by
  sorry

lemma IsPathGraph.setOf_isLeafEdge_eq (hP : P.IsPathGraph) (hne : E(P).Nonempty) :
    {e | P.IsLeafEdge e} = {hP.firstEdge hne, hP.lastEdge hne} := by
  sorry

lemma IsPathGraph.eDegree_first_le_one (hP : P.IsPathGraph) :
    P.eDegree hP.first ≤ 1 := by
  sorry

@[simp, grind →]
lemma IsPathGraph.eDegree_first_eq_one (hP : P.IsPathGraph) (hne : E(P).Nonempty) :
    P.eDegree hP.first = 1 := by
  rw [eDegree_eq_one_iff]
  exact hP.isLeaf_first hne

@[simp, grind →]
lemma IsPathGraph.eDegree_last_eq_one (hP : P.IsPathGraph) (hne : E(P).Nonempty) :
    P.eDegree hP.last = 1 := by
  rw [eDegree_eq_one_iff]
  exact hP.isLeaf_last hne

-- probably want some generic "external/internal vxs/edges" for forests
-- external vxs are just leaves
-- internal vxs are non-leaves
-- external edges are edges for which at least one endpoint is a leaf
-- internal edges are edges for which both endpoints are not leaves

-- TODO: MOVE ALL LEAF LEMMAS

@[simp, grind →]
lemma IsPendant.edge_mem (h : G.IsPendant e x) : e ∈ E(G) :=
  h.isNonloopAt.edge_mem

@[simp, grind →]
lemma IsPendant.vertex_mem (h : G.IsPendant e x) : x ∈ V(G) :=
  h.isNonloopAt.vertex_mem

@[simp, grind →]
lemma IsPendant.isLeafEdge (h : G.IsPendant e x) : G.IsLeafEdge e :=
  ⟨x, h⟩

@[simp, grind →]
lemma IsPendant.inc (h : G.IsPendant e x) : G.Inc e x :=
  h.isNonloopAt.inc

@[simp, grind →]
lemma IsLeafEdge.edge_mem (he : G.IsLeafEdge e) : e ∈ E(G) := by
  obtain ⟨x, h⟩ := he
  exact h.edge_mem

@[grind =>, simp]
lemma not_isPendant_of_not_isLeafEdge (he : ¬ G.IsLeafEdge e) (x : α) : ¬ G.IsPendant e x := by
  contrapose he
  exact ⟨x, he⟩

@[grind]
def IsNonleafEdge (G : Graph α β) (e : β) :=
    ∃ x y, ¬ G.IsPendant e x ∧ ¬ G.IsPendant e y ∧ G.IsLink e x y

namespace IsNonleafEdge

@[grind ., simp]
lemma edge_mem (he : G.IsNonleafEdge e) : e ∈ E(G) := by
  obtain ⟨_, _, _, _, h⟩ := he
  exact h.edge_mem

@[grind =>, simp]
lemma not_isPendant (he : G.IsNonleafEdge e) (x : α) : ¬ G.IsPendant e x := by
  intro bad
  obtain ⟨y, z, hey, hez, heyz⟩ := he
  obtain (rfl|rfl) := bad.inc.eq_or_eq_of_isLink heyz
    <;> contradiction

@[grind →, simp]
lemma not_isLeafEdge (he : G.IsNonleafEdge e) : ¬ G.IsLeafEdge e := by
  simp [IsLeafEdge]
  exact he.not_isPendant

end IsNonleafEdge

@[grind →, simp]
lemma IsLeafEdge.not_isNonleafEdge (h : G.IsLeafEdge e) : ¬ G.IsNonleafEdge e := by
  contrapose h
  exact h.not_isLeafEdge

lemma isNonLeafEdge_of_not_isLeafEdge (he : e ∈ E(G)) (h : ¬ G.IsLeafEdge e) :
    G.IsNonleafEdge e := by
  rw [edge_mem_iff_exists_isLink] at he
  obtain ⟨x, y, hexy⟩ := he
  refine ⟨x, y, ?_, ?_, hexy⟩
   <;> exact not_isPendant_of_not_isLeafEdge h _

lemma isLeafEdge_of_not_isNonleafEdge (he : e ∈ E(G)) (h : ¬ G.IsNonleafEdge e) :
    G.IsLeafEdge e := by
  contrapose h
  exact isNonLeafEdge_of_not_isLeafEdge he h

lemma not_isNonleafEdge_iff_isLeafEdge (he : e ∈ E(G)) :
    ¬ G.IsNonleafEdge e ↔ G.IsLeafEdge e :=
  ⟨isLeafEdge_of_not_isNonleafEdge he, IsLeafEdge.not_isNonleafEdge⟩

lemma not_isLeafEdge_iff_isNonleafEdge (he : e ∈ E(G)) :
    ¬ G.IsLeafEdge e ↔ G.IsNonleafEdge e :=
  ⟨isNonLeafEdge_of_not_isLeafEdge he, IsNonleafEdge.not_isLeafEdge⟩


lemma IsPathGraph.isForest (hP : P.IsPathGraph) : P.IsForest := by
  obtain ⟨p, hp⟩ := hP
  rw [hp.2]
  exact hp.1.toGraph_isForest

lemma IsPathGraph.isTree (hP : P.IsPathGraph) : P.IsTree where
  isForest := hP.isForest
  connected := hP.connected

lemma IsPathGraph.eq_first_or_last_of_eDegree_le_one (hP : P.IsPathGraph) (hxP : x ∈ V(P))
    (hdeg : P.eDegree x ≤ 1) : x = hP.first ∨ x = hP.last := by
  have hp := hP.choose_spec
  set p := hP.choose
  change x = p.first ∨ x = p.last
  refine hp.1.isTrail.eq_first_or_last_of_eDegree_le_one ?_ hdeg
  simp [hp.2, toGraph_vertexSet] at hxP
  assumption

lemma IsPathGraph.eq_first_or_last_of_eDegree_eq_one (hP : P.IsPathGraph) (hdeg : P.eDegree x = 1) :
    x = hP.first ∨ x = hP.last := by
  refine hP.eq_first_or_last_of_eDegree_le_one ?_ (le_of_eq hdeg)
  rw [eDegree_eq_one_iff] at hdeg
  exact hdeg.mem

lemma IsPathGraph.degreePos (hP : P.IsPathGraph) (hne : E(P).Nonempty) : P.DegreePos := by
  sorry

lemma IsPathGraph.eDegree_eq_two (hP : P.IsPathGraph) (hxP : x ∈ V(P)) (hne_first : x ≠ hP.first)
    (hne_last : x ≠ hP.last) : P.eDegree x = 2 := by
  sorry

lemma IsPathGraph.maxDegreeLE_two (hP : P.IsPathGraph) : P.MaxDegreeLE 2 := by
  obtain (hempty|hne) := em' (E(P).Nonempty)
  · sorry
  rw [maxDegreeLE_iff']
  intro x hxP
  obtain (h|h) := em (x = hP.first ∨ x = hP.last)
  · obtain (rfl|rfl) := h
      <;> [rw [hP.isLeaf_first hne |>.eDegree] ; rw [hP.isLeaf_last hne |>.eDegree]]
      <;> enat_to_nat <;> omega
  simp at h
  exact le_of_eq <| hP.eDegree_eq_two hxP h.1 h.2

lemma IsPathGraph.eDegree_eq_one_or_two (hP : P.IsPathGraph) (hne : E(P).Nonempty)
    (hxP : x ∈ V(P)) :
    P.eDegree x = 1 ∨ P.eDegree x = 2 := by
  sorry

lemma IsPathGraph.eq_first_or_last_or_inner (hP : P.IsPathGraph) (hxP : x ∈ V(P)) :
    x = hP.first ∨ x = hP.last ∨ P.eDegree x = 2 := by
  obtain (h|h) := em (x = hP.first ∨ x = hP.last)
  · grind
  simp at h
  right; right
  exact hP.eDegree_eq_two hxP h.1 h.2

-- `IsAugmenter` takes the place of augmenting paths; it is a strict generalization.
structure IsAugmenter (G : Graph α β) (M : Set β) (P : Graph α β) : Prop where
  le : P ≤ G
  -- effectively, MaxDegreeLE 2, but also we have no isolated vertices
  eDegree_eq_one_or_two : ∀ ⦃x⦄, x ∈ V(P) → P.eDegree x = 1 ∨ P.eDegree x = 2
  -- there is at least one leaf (this shows that there is at least one augmenting path in our graph)
  exists_isLeaf : ∃ x, P.IsLeaf x
  -- all internal vx of P are matched by M, by edges of P
  match_nonleaf : ∀ ⦃x⦄, P.eDegree x = 2 → x ∈ V(P, M)
  -- neither of the leaf vxs of P are matched by M
  no_match_leaf : ∀ ⦃x⦄, P.eDegree x = 1 → x ∉ V(G, M)

attribute [grind →, grind <=]
    IsAugmenter.le IsAugmenter.eDegree_eq_one_or_two IsAugmenter.exists_isLeaf IsAugmenter.match_nonleaf
    IsAugmenter.no_match_leaf

lemma IsAugmenter.matched_vertexSet_eq (hP : G.IsAugmenter M P) :
    V(P, M) = {x ∈ V(P) | P.eDegree x = 2} := by
  ext x
  refine ⟨?_, ?_⟩
  · intro hx
    refine ⟨by grind, ?_⟩
    by_contra! bad
    replace bad : P.eDegree x = 1 := by
      have := hP.eDegree_eq_one_or_two (incVertexSet_subset _ _ hx)
      grind only
    exact hP.no_match_leaf bad (incVertexSet_mono hP.le _ hx)
  grind

lemma IsAugmenter.matched_vertexSet_eq' (hP : G.IsAugmenter M P) :
    V(P, E(P) ∩ M) = {x ∈ V(P) | P.eDegree x = 2} := by
  rw [← hP.matched_vertexSet_eq, inter_comm, incVertexSet_inter_edgeSet]

lemma IsAugmenter.maxDegreeLE_two (hP : G.IsAugmenter M P) : P.MaxDegreeLE 2 := by
  rw [maxDegreeLE_iff']
  intro x hx
  obtain (h|h) := hP.eDegree_eq_one_or_two hx
    <;> (enat_to_nat!; omega)

lemma IsAugmenter.degreePos (hP : G.IsAugmenter M P) : P.DegreePos := by
  rw [degreePos_iff']
  intro x hx
  obtain (h|h) := hP.eDegree_eq_one_or_two hx
    <;> (enat_to_nat!; omega)

lemma IsAugmenter.edgeSet_nonempty (hP : G.IsAugmenter M P) : E(P).Nonempty := by
  have ⟨x, e, hex⟩ := hP.exists_isLeaf
  exact ⟨e, hex.edge_mem⟩

lemma IsAugmenter.diff_matching_isMatching [P.Loopless] (hP : G.IsAugmenter M P) :
    P.IsMatching (E(P) \ M) where
  subset := by
    grw [diff_subset]
  disjoint e f he hf hne := by
    rw [disjoint_left]
    intro x hxe hxf
    change e ∈ E(P, x) at hxe
    change f ∈ E(P, x) at hxf
    have deg : P.eDegree x = 2 := by
      refine (hP.maxDegreeLE_two x).antisymm ?_
      rw [eDegree_eq_encard_inc, Nat.cast_ofNat, two_le_encard_iff_nontrivial]
      refine ⟨e, hxe, f, hxf, hne⟩
    have h_incEdges : E(P, x) = {e, f} := by
      symm
      rw [←Nat.cast_ofNat, eDegree_eq_encard_inc] at deg
      have fin : E(P, x).Finite := by
        exact finite_of_encard_le_coe (le_of_eq deg)
      refine eq_of_subset_of_ncard_le ?_ ?_ ‹_›
      · rintro e' (rfl|rfl) <;> assumption
      apply congr_arg ENat.toNat at deg
      simp [← ncard_def] at deg
      grw [deg, ncard_pair hne]
    have bad := hP.match_nonleaf deg
    simp at bad
    obtain ⟨e', he'M, he'⟩ := bad
    change e' ∈ E(P, x) at he'
    simp [h_incEdges] at he'
    obtain (rfl|rfl) := he'
      <;> [exact he.2 ‹_›; exact hf.2 ‹_›]

--
lemma IsAugmenter.vertexSet_disjoint (hM : G.IsMatching M) (hP : G.IsAugmenter M P) :
    Disjoint V(P) V(G, M \ E(P)) := by
  rw [disjoint_left]
  intro x hxP hxGM'
  have hxGM : x ∈ V(G, M) := by
    simp at hxGM'
    obtain ⟨e, he⟩ := hxGM'
    refine ⟨e, he.1.1, he.2⟩
  obtain (h|h) := hP.eDegree_eq_one_or_two hxP
  · exact hP.no_match_leaf ‹_› hxGM
  have M_diff_matching : G.IsMatching (M \ E(P)) :=
    hM.anti_right diff_subset
  have P_matching : P.IsMatching (E(P) ∩ M) :=
    hM.anti_left' hP.le
  have hxPM : x ∈ V(P, E(P) ∩ M) := by
    have ⟨e, he⟩ := hP.match_nonleaf h
    exact ⟨e, ⟨he.2.edge_mem, he.1⟩, he.2⟩
  have ⟨e, he, e_unique⟩ := hM.existsUnique_covering_edge hxGM
  obtain ⟨e', he', -⟩ := M_diff_matching.existsUnique_covering_edge hxGM'
  obtain ⟨f, hf, -⟩ := P_matching.existsUnique_covering_edge hxPM
  simp at e_unique he he' hf
  have : e' = f := by
    rw [e_unique _ he'.1.1 he'.2, e_unique _ hf.1.2 (hf.2.of_le hP.le)]
  rw [this] at he'
  exact he'.1.2 hf.2.edge_mem

/-- Given a matching M and an augmenting path P for M, we can get back a larger matching --/
lemma IsAugmenter.symmDiff_matching_isMatching [P.Loopless] (hM : G.IsMatching M)
    (hP : G.IsAugmenter M P) : G.IsMatching (E(P) ∆ M) := by
  rw [symmDiff_comm]
  have disj : P.StronglyDisjoint (Subgraph.ofEdge G (M \ E(P))) := by
    refine ⟨?_, ?_⟩
    · simp
      exact hP.vertexSet_disjoint hM
    rw [disjoint_left]
    simp
    grind only
  have P_matching : P.IsMatching (E(P) \ M) := hP.diff_matching_isMatching
  set G' := Subgraph.ofEdge G (M \ E(P))
  have G'_matching : G'.val.IsMatching (M \ E(P)) := by
    have matching : G.IsMatching (M \ E(P)) :=
      hM.anti_right diff_subset
    refine matching.anti_left G'.le ?_
    simp [G']
    grw [diff_subset, hM.subset]
  have := P_matching.union G'_matching disj
  rw [symmDiff_comm, Set.symmDiff_def]
  refine this.mono_left ?_
  refine Graph.union_le hP.le G'.le

lemma IsAugmenter.diff_matching_vertexSet [P.Loopless] (hM : G.IsMatching M)
    (hP : G.IsAugmenter M P) : V(P, E(P) \ M) = V(P) := by
  -- every degree-2 vertex gets matched by the other edge
  -- every degree-1 vertex must have previously been unmatched, and hence must now be matched
  refine eq_of_subset_of_subset (incVertexSet_subset _ _) ?_
  intro x hxP
  obtain (deg|deg) := hP.eDegree_eq_one_or_two hxP
  · -- degree 1
    have h : P.eDegree x = 1 := deg
    rw [eDegree_eq_encard_inc, encard_eq_one] at h
    obtain ⟨e, heq⟩ := h
    have he : P.Inc e x := by
      change e ∈ E(P, x)
      simp [heq]
    have he_notMem_M : e ∉ M := by
      intro heM
      refine hP.no_match_leaf deg ?_
      refine ⟨e, heM, he.of_le hP.le⟩
    refine ⟨e, ⟨he.edge_mem, he_notMem_M⟩, he⟩
  -- degree 2
  have ⟨e, he⟩ := hP.match_nonleaf deg
  rw [eDegree_eq_encard_inc] at deg
  symm at deg; apply le_of_eq at deg
  rw [two_le_encard_iff_nontrivial] at deg
  have ⟨f, hf⟩ := deg.exists_ne e
  refine ⟨f, ⟨hf.1.edge_mem, ?_⟩, hf.1⟩
  intro hfM
  have := hM.disjoint hfM he.1 hf.2
  rw [disjoint_left] at this
  exact this (hf.1.of_le hP.le) (he.2.of_le hP.le)

-- TODO: move
lemma incVertexSet_mono_right {F F' : Set β} (G : Graph α β) (hsub : F ⊆ F') :
    V(G, F) ⊆ V(G, F') := by
  rintro x ⟨e, heF, hex⟩
  refine ⟨e, hsub heF, hex⟩

lemma IsAugmenter.symmDiff_matching_vertexSet [P.Loopless] (hM : G.IsMatching M)
    (hP : G.IsAugmenter M P) : V(P, E(P) ∆ M) = V(P) := by
  refine eq_of_subset_of_subset (incVertexSet_subset _ _) ?_
  grw [Set.symmDiff_def, ← incVertexSet_mono_right _ (subset_union_left),
    hP.diff_matching_vertexSet hM]

-- TODO: rename; what a mouthful
-- TODO: also, is this even useful in this form? statements about encard ≤ encard are really weak...
--       we really want to say that there is at least one more element.
-- this can't even be _ < _ anymore, since we are no longer assuming a path (which is guaranteed to
-- be finite).
lemma IsAugmenter.matching_encard_add_one_le_diff_matching_encard [P.Loopless]
    (hM : G.IsMatching M) (hP : G.IsAugmenter M P) : (E(P) ∩ M).encard + 1 ≤ (E(P) \ M).encard := by
  -- (E(P) \ M) matches all of V(P)
  -- so 2 * |E(P) \ M| = |V(P)|
  -- meanwhile, (E(P) ∩ M) matches V(P) \ {P.first, P.last}
  -- so 2 * |E(P) ∩ M| = |V(P) \ {P.first, P.last}| = |V(P)| - 2
  -- so |E(P) \ M| = 1 + |E(P) ∩ M|
  have M'_isMatching : P.IsMatching (E(P) \ M) := diff_matching_isMatching hP
  have M'_matched_vertexSet : V(P, E(P) \ M) = V(P) := hP.diff_matching_vertexSet hM
  have M'_encard : 2 * (E(P) \ M).encard = V(P).encard := by
    rw [← M'_isMatching.matched_vertexSet_encard_eq, M'_matched_vertexSet]
  have M_matching : P.IsMatching (E(P) ∩ M) :=
    hM.anti_left' hP.le
  have M_matched_vertexSet : V(P, E(P) ∩ M) = {x ∈ V(P) | P.eDegree x = 2} :=
    hP.matched_vertexSet_eq'
  have M_encard : 2 * (E(P) ∩ M).encard = V(P, E(P) ∩ M).encard :=
    M_matching.matched_vertexSet_encard_eq.symm
  obtain (h_top|h_ne_top) := em (V(P).encard = ⊤)
  · rw [h_top, ENat.mul_eq_top_iff] at M'_encard
    obtain (h|h) := M'_encard
    · enat_to_nat
    rw [h.2]
    exact le_top
  have VP_fin : V(P).Finite := by
    rw [← ne_eq, encard_ne_top_iff] at h_ne_top
    assumption
  have VPM_fin : V(P, E(P) ∩ M).Finite :=
    VP_fin.subset (incVertexSet_subset _ _)
  suffices hssub : V(P, E(P) ∩ M) ⊂ V(P)
  · have hlt := VPM_fin.encard_lt_encard hssub
    enat_to_nat!; omega
  rw [ssubset_iff_exists]
  refine ⟨incVertexSet_subset _ _, ?_⟩
  obtain ⟨x, hx⟩ := hP.exists_isLeaf
  refine ⟨x, hx.mem, ?_⟩
  rintro ⟨e, hePM, hex⟩
  refine hP.no_match_leaf hx.eDegree ?_
  refine ⟨e, hePM.2, hex.of_le hP.le⟩

lemma IsAugmenter.matching_encard_add_one_le_symmDiff_matching_encard [P.Loopless]
    (hM : G.IsMatching M) (hP: G.IsAugmenter M P) : M.encard + 1 ≤ (E(P) ∆ M).encard := by
  have hdisj : Disjoint (E(P) \ M) (M \ E(P)) := disjoint_sdiff_sdiff
  conv_rhs => rw [Set.symmDiff_def, encard_union_eq hdisj, add_comm]
  conv_lhs => rw [show M = (M \ E(P)) ∪ (M ∩ E(P)) by grind, encard_union_eq disjoint_sdiff_inter,
    add_assoc]
  obtain (h_top|h_ne_top) := em ((M \ E(P)).encard = ⊤)
  · simp only [h_top, top_add, le_refl]
  refine (ENat.add_le_add_iff_left h_ne_top).mpr ?_
  rw [inter_comm]
  exact hP.matching_encard_add_one_le_diff_matching_encard hM

-- for finite graphs then (or more generally, graphs with finite matching number),
-- there must not be an augmenting path whenever we have a max matching
lemma IsMaxMatching.not_isAugmenter [G.EdgeFinite]
    (hM : G.IsMaxMatching M) (P : Graph α β) [P.Loopless] :
    ¬ G.IsAugmenter M P := by
  intro hP
  -- TODO: wish this would be automatically detected by `enat_to_nat`
  have M_encard_fin : M.encard < ⊤ := by
    rw [encard_lt_top_iff]
    refine Finite.subset edgeSet_finite hM.subset
  have M'_isMatching : G.IsMatching (E(P) ∆ M) :=
    hP.symmDiff_matching_isMatching hM.toIsMatching
  have := hP.matching_encard_add_one_le_symmDiff_matching_encard hM.toIsMatching
  have := hM.max _ M'_isMatching
  enat_to_nat!; omega

/-
 sketch of other direction:
 first, for matchings M, M' on G, let G' := Subgraph.ofEdges G (M ∆ M')
 then, components of G' must be one of:
 * isolated vertex
 * even cycle with edges alternating b/n M and M'
 * paths with edges alternating b/n M and M'

 showing that the components are cycles / paths shouldnt be hard; more attention needs to be paid
 perhaps to "edges alternating b/n M and M'"

 now, suppose M is not a max matching for G. then there exists a matching M' with |M'| > |M|.
 so there must be a component which is a path and has more edges from M' than from M;
 thus this component must be an augmenting path.
-/

@[simp]
lemma Subgraph.ofEdge_inc_iff (F : Set β) :
    (Subgraph.ofEdge G F).val.Inc e x ↔ e ∈ F ∧ G.Inc e x := by
  simp [Inc]

@[simp]
lemma Subgraph.ofEdge_incEdges_eq (F : Set β) :
    E(Subgraph.ofEdge G F, x) = E(G, x) ∩ F := by
  ext e; simp [IncEdges]; rw [and_comm]

lemma IsCycle.regular (h : G.IsCycle) : G.Regular 2 := by
  rw [isCycle_iff_exists_isCyclicWalk_eq] at h
  obtain ⟨C, hC, heq⟩ := h
  rw [← heq]
  exact hC.toGraph_regular

private
lemma symmDiff_matching_edge_at
    [G.Loopless]
    (hM : G.IsMatching M) (hM' : G.IsMatching M')
    (hle : H ≤ Subgraph.ofEdge G (M ∆ M'))
    (hx : x ∈ V(H)) (hex : e ∈ E(H, x)) (hfx : f ∈ E(H, x)) (hne : e ≠ f) (heM : e ∈ M) :
    f ∈ M' := by
  have h_edge : ∀ e ∈ E(H), (e ∈ M \ M') ∨ (e ∈ M' \ M) := by
    intro e he
    have := edgeSet_mono hle
    simp at this
    apply this.2 at he
    rw [Set.symmDiff_def] at he
    exact he
  by_contra! hfM
  replace hfM : f ∈ M := by
    have := h_edge f (H.incEdges_subset x hfx)
    grind only [= mem_diff]
  -- here is a case where matching is baring its teeth...
  sorry



-- TODO: what is the easiest way of proving this?
private
lemma symmDiff_matching_cycle_edge_encard
    [G.Loopless]
    (hM : G.IsMatching M) (hM' : G.IsMatching M')
    (hHP : H.IsCompOf (Subgraph.ofEdge G (M ∆ M')))
    (h_cycle : H.IsCycle) :
    (E(H) ∩ M).encard = (E(H) ∩ M').encard := by

  -- any edge in H must be in exactly one of M or M'
  have h_edge : ∀ e ∈ E(H), (e ∈ M \ M') ∨ (e ∈ M' \ M) := by
    intro e he
    have := edgeSet_mono hHP.le
    simp at this
    apply this.2 at he
    rw [Set.symmDiff_def] at he
    exact he

  have _ : H.Loopless :=
    ‹G.Loopless›.mono (hHP.le.trans <| Subgraph.le _)

  have h_vx : ∀ x ∈ V(H), x ∈ V(H, M) ∧ x ∈ V(H, M') := by
    intro x hx
    -- H is 2-regular, so there are two edges
    have hx_edges := h_cycle.regular hx
    -- TODO: can you avoid needing `change` here?
    change H.eDegree x = 2 at hx_edges
    rw [eDegree_eq_encard_inc, encard_eq_two] at hx_edges
    obtain ⟨e, f, hne, heq⟩ := hx_edges
    wlog heM : e ∉ M generalizing e f with aux
    · refine aux f e hne.symm (by rw [heq, pair_comm]) ?_
      simp at heM
      intro hfM
      have h_encard : E(H ↾ M, x).encard = 2 := by
        sorry
      have h_encard₂ : E(G ↾ M, x).encard = 1 := by
        rw [← eDegree_eq_encard_inc, hM.eDegree_eq_one]
        sorry
      have h_sub : E(H ↾ M, x) ⊆ E(G ↾ M, x) := by
        refine incEdges_mono ?_ _
        rw [le_edgeRestrict_iff]
        refine ⟨edgeRestrict_le.trans <| hHP.le.trans <| Subgraph.le _, ?_⟩
        simp
      apply encard_le_encard at h_sub
      enat_to_nat! <;> omega
    sorry
  -- direct soln might be easiest
  -- for all x ∈ H, (H ↾ M).eDegree x = (H ↾ M').eDegree x = 1
  --

  -- suppose not. then wlog suppose |E(H) ∩ M| < |E(H) ∩ M'|.
  -- now, let e ∈ E(H) ∩ (M' \ M)
  --
  sorry

lemma exists_isAugmenter_of_matching_encard_lt
    [G.Loopless]
    (hM : G.IsMatching M) (hM' : G.IsMatching M') (hlt : M.encard < M'.encard) :
    ∃ P, G.IsAugmenter M P := by
  let P := Subgraph.ofEdge G (M ∆ M')
  have P_loopless : P.val.Loopless :=
    ‹G.Loopless›.mono P.2
  have P_degPos : P.val.DegreePos := by
    rw [degreePos_iff']
    intro x ⟨e, he⟩
    grw [← ENat.one_le_iff_ne_zero, ← encard_inc_le_eDegree, one_le_encard_iff_nonempty,
      Subgraph.ofEdge_incEdges_eq]
    refine ⟨e, he.2, he.1⟩
  have P_maxDegreeLE : P.val.MaxDegreeLE 2 := by
    rw [maxDegreeLE_iff']
    intro x hx
    simp only [eDegree_eq_encard_inc, P, Subgraph.ofEdge_incEdges_eq]
    rw [show E(G, x) ∩ M ∆ M' = E(G, x) ∩ (M \ M') ∪ E(G, x) ∩ (M' \ M) by grind]
    rw [encard_union_eq (by grind)]
    rw [show (2 : ℕ) = (1 : ℕ∞) + 1 by enat_to_nat]
    refine add_le_add ?_ ?_
    all_goals
      rw [← incEdges_edgeRestrict]
      refine IsMatching.incEdges_encard_le_one ?_ _
      exact IsMatching.anti_right ‹_› diff_subset
  have P_leaf : ∃ x, P.val.IsLeaf x := by
    -- cardinality argument?
    -- oh god this is going to be so painful if |M'| = ⊤
    -- suppose there are no leaves.
    -- then the graph must be 2-regular, and all components must be cycles
    -- per component, if the component is a cycle, then the number of edges in M
    -- must equal the number of edges in M'
    -- so since every component is a cycle, we must have |M| = |M'|, a contradiction.
    sorry

  -- TODO:
  -- not just directly P, we want just the one augmenting path that must exist?
  obtain ⟨P', hP'P, hP'_encard⟩ :
     ∃ P' : Graph α β, P'.IsCompOf P ∧ (E(P') ∩ M).encard < (E(P') ∩ M').encard := by
    sorry
  have hP'_path : P'.IsPathGraph := by
    sorry

  have P'_deg : ∀ x ∈ V(P'), P'.eDegree x = 1 ∨ P'.eDegree x = 2 := by
    intro x hx
    have := P_maxDegreeLE x
    rw [degreePos_iff'] at P_degPos
    have := P_degPos (vertexSet_mono hP'P.le hx)
    rw [hP'P.isClosedSubgraph.eDegree_eq hx]
    enat_to_nat! <;> omega
  have _ : P'.Loopless := ‹P.val.Loopless›.mono hP'P.le

  refine ⟨P', ?_⟩
  constructor
  · exact hP'P.le.trans P.2
  · exact P'_deg
  · -- P' is a path, so we must have a leaf?
    refine ⟨hP'_path.first, hP'_path.isLeaf_first ?_⟩
    rw [← encard_ne_zero]
    -- TODO: this is as annoying case where i wish we could just have a tactic that clears this
    -- obligation.
    -- we have (E(P') ∩ M).encard < (E(P') ∩ M').encard, and we want to show that E(P').encard ≠ 0
    intro bad
    have : (E(P') ∩ M').encard ≤ E(P').encard :=
      encard_le_encard (inter_subset_left)
    enat_to_nat! <;> omega

  · intro x hx
    -- one of the two edges must be from M
    rw [eDegree_eq_encard_inc, encard_eq_two] at hx
    obtain ⟨e, f, hne, heq⟩ := hx
    wlog heM : e ∈ M generalizing e f with aux
    · specialize aux f e hne.symm (by rw [heq, pair_comm])
      have heM' : e ∈ M' := by
        sorry
      have hfM : f ∈ M := by
        sorry
      exact aux hfM
    refine ⟨e, heM, ?_⟩
    change e ∈ E(P', x)
    simp [heq]
  -- there is at least one augmenting path...
  -- handshake?
  -- 2|E(P')| = ∑ P'.eDegree x
  -- 2|E(P' ↾ M)| = ∑ (P' ↾ M).eDegree x = ∑ |E(P', x) ∩ M|
  -- 2|E(P' ↾ M')| = ∑ (P' ↾ M').eDegree x = ∑ |E(P', x) ∩ M'|
  -- 2|E(P')| = 2|E(P' ↾ M)| + 2|E(P' ↾ M')|

  sorry




/-! ### Structure of graph from maximal matching -/

def Inessential (G : Graph α β) (x : α) : Prop :=
  ∃ M, G.IsMaxMatching M ∧ x ∉ V(G, M)

structure IsOddCompOf (H G : Graph α β) extends H.IsCompOf G where
  finite : V(H).Finite
  odd : Odd V(H).encard

def oddComponents (G : Graph α β) : Set (Graph α β) :=
  {H | H.IsOddCompOf G}
