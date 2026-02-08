import Matroid.Graph.Matching.Defs

variable {α β : Type*} {G H C : Graph α β} {S X Y : Set α} {M M' : Set β} {u v x y z : α} {e f : β}
  {hM : G.IsMatching M} {P P' : WList α β}

open Set symmDiff WList

namespace Graph

def coverNumberSet (G : Graph α β) : Set ℕ∞ :=
  {n | ∃ S, G.IsCover S ∧ n = S.encard}

@[simp]
lemma coverNumberSet_eq : G.coverNumberSet = {n | ∃ S, G.IsCover S ∧ n = S.encard} := rfl

abbrev matchingNumberSet (G : Graph α β) : Set ℕ∞ :=
  {n | ∃ M, G.IsMatching M ∧ n = M.encard}

@[simp]
lemma matchingNumberSet_eq : G.matchingNumberSet = {n | ∃ M, G.IsMatching M ∧ n = M.encard} := rfl

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


lemma IsCover.isMinCover_of_encard_eq (hC : G.IsCover S) (h : S.encard = τ(G)) :
    G.IsMinCover S where
  toIsCover := hC
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

lemma IsCover.intersect_endSet_nonempty (hC : G.IsCover S) (he : e ∈ E(G)) :
    Nonempty ↑(S ∩ V(G, e)) := by
  have ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  obtain (h|h) := hC.mem_or_mem_of_isLink hxy
    <;> [refine ⟨x, ?_⟩ ; refine ⟨y, ?_⟩]
    <;> tauto_set

noncomputable def IsMatching.mapToCover (hM : G.IsMatching M) (hC : G.IsCover S) : M → S := by
  -- we should be able to arbitrarily choose either vertex for any e ∈ M
  intro ⟨e, he⟩
  have heE : e ∈ E(G) := hM.subset he
  -- take ends, cap with S?
  have nonempty := hC.intersect_endSet_nonempty heE
  obtain ⟨x, hx⟩ := Classical.choice nonempty
  refine ⟨x, hx.1⟩

-- set_option pp.proofs true in
lemma IsMatching.mapToCover_inj (hM : G.IsMatching M) (hC : G.IsCover S) :
    Function.Injective (hM.mapToCover hC) := by
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
lemma IsMatching.mapToCover_inc (hM : G.IsMatching M) (hC : G.IsCover S) (he : e ∈ M) :
    G.Inc e (hM.mapToCover hC ⟨e, he⟩) := by
  simp only [mapToCover]
  set x := (Classical.choice (IsCover.intersect_endSet_nonempty hC (hM.subset he)))
  have hxE : ↑x ∈ V(G, e) := x.2.2
  rwa [← mem_endSet_iff]

lemma matchingNumber_le_coverNumber : ν(G) ≤ τ(G) := by
  simp only [matchingNumber, coverNumber]
  simp only [le_sInf_iff, sSup_le_iff]
  rintro t ⟨C, hC, rfl⟩ n ⟨M, hM, rfl⟩
  have solver := (hM.mapToCover_inj hC).encard_range
  simp only [ENat.card_coe_set_eq, range] at solver
  refine le_trans solver ?_
  rw [show C.encard = (univ : Set ↑C).encard by simp]
  refine encard_le_encard (by grind)

lemma IsMatching.mapToCover_range_eq_of_encard_eq [G.Finite]
    (hC : G.IsCover S) (hM : G.IsMatching M) (h : S.encard = M.encard) :
    range (hM.mapToCover hC) = ⊤ := by
  sorry

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
  have := hS_H.subgraph_cover hle
  sorry

end Graph

namespace WList
open Graph

def pathCover : WList α β → Set α
| nil _ => ∅
| cons _ _ (nil v) => {v}
| cons _ _ (cons v _ w) => insert v (pathCover w)

lemma pathCover_subset (P : WList α β) : P.pathCover ⊆ V(P) := by
  match P with
  | nil _ => simp [pathCover]
  | cons _ _ (nil v) => simp [pathCover]
  | cons _ _ (cons v _ w) =>
    simp only [pathCover, cons_vertexSet]
    exact subset_trans (insert_subset_insert w.pathCover_subset) <| subset_insert ..

lemma pathCover_inc {P : WList α β} (hw : P.WellFormed) (he : e ∈ E(P)) :
    e ∈ E(P.toGraph, P.pathCover) := by
  match P with
  | nil _ => simp at he
  | cons u f (nil v) =>
    simp only [cons_edgeSet, nil_edgeSet, insert_empty_eq, mem_singleton_iff,
      mem_setIncEdges_iff] at he ⊢
    subst f
    use v, by simp [pathCover], u
    simp [hw.toGraph_isLink, isLink_cons_iff']
  | cons u e₁ (cons v e₂ w) =>
    simp only [cons_edgeSet, mem_insert_iff, mem_edgeSet_iff] at he
    obtain rfl | rfl | h := he <;> simp only [pathCover, mem_setIncEdges_iff, mem_insert_iff,
    exists_eq_or_imp]
    · left
      use u
      simp [hw, isLink_cons_iff']
    · left
      use w.first
      simp [hw, isLink_cons_iff']
    right
    have hwW : w.WellFormed := hw.of_cons.of_cons
    obtain ⟨x, hx, y, h⟩ := pathCover_inc hwW h
    rw [hwW.toGraph_isLink] at h
    use x, hx, y
    simp [hw.toGraph_isLink, isLink_cons_iff', h]

lemma pathCover_isCover (hw : P.WellFormed) : P.toGraph.IsCover P.pathCover where
  subset := by
    rw [toGraph_vertexSet]
    exact P.pathCover_subset
  cover e he := pathCover_inc hw (by simpa using he)

lemma pathCover_ncard {P : WList α β} (hw : P.vertex.Nodup) :
    P.pathCover.ncard = V(P).ncard / 2 := by
  match P with
  | nil _ => simp [pathCover]
  | cons _ _ (nil v) =>
    simp only [pathCover, ncard_singleton, cons_vertexSet, nil_vertexSet]
    simp only [cons_vertex, nil_vertex, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_false_eq_true, List.nodup_nil, and_self, and_true] at hw
    rw [ncard_pair hw]
  | cons _ _ (cons v _ w) =>
    simp only [cons_vertex, List.nodup_cons, List.mem_cons, mem_vertex, not_or, pathCover,
      cons_vertexSet] at hw ⊢
    obtain ⟨⟨hne, huw⟩, hvw, hw⟩ := hw
    have : w.pathCover.Finite := w.vertexSet_finite.subset w.pathCover_subset
    rw [ncard_insert_of_notMem (fun h ↦ hvw <| w.pathCover_subset h) this,
      ncard_insert_of_notMem (by simp [hne, huw]) (by simp),
      ncard_insert_of_notMem (by simpa) (by simp), pathCover_ncard hw]
    omega

def pathMatching : WList α β → Set β
| nil _ => ∅
| cons _ e (nil _) => {e}
| cons _ e (cons _ _ w) => insert e (pathMatching w)

lemma pathMatching_subset (P : WList α β) : P.pathMatching ⊆ E(P) := by
  match P with
  | nil _ => simp [pathMatching]
  | cons _ e (nil _) => simp [pathMatching]
  | cons _ e (cons _ _ w) =>
    simp only [pathMatching, cons_edgeSet]
    exact insert_subset_insert <| w.pathMatching_subset.trans <| subset_insert ..

end WList

-- lemma Graph.IsPath.pathMatching_isMatching (hP : G.IsPath P) :
--     P.toGraph.IsMatching P.pathMatching where
--   subset := by
--     rw [toGraph_edgeSet]
--     exact P.pathMatching_subset
--   disjoint e f he hf hne := by
--     match P with
--     | nil _ => simp [pathMatching] at he hf
--     | cons _ e (nil _) => simp_all [pathMatching]
--     | cons u a (cons v b w) =>
--     obtain ⟨⟨hw, hvwf, hvw⟩, hauv, huv, huw⟩ := by simpa [← ne_eq] using hP
--     obtain ⟨⟨-, -, hbw⟩, -, hab, haw⟩ := by simpa [← ne_eq] using hP.isTrail
--     simp only [pathMatching, mem_insert_iff] at he hf
--     rw [disjoint_iff_forall_notMem]
--     intro x ⟨x', hx⟩ ⟨y', hy⟩
--     -- simp only [hP.isWalk.wellFormed.toGraph_isLink, isLink_cons_iff', first_cons] at hx hy
--     obtain (rfl| he) := he <;> obtain (rfl| hf) := hf
--     · exact hne rfl
--     · replace hf := w.pathMatching_subset hf
--       have := by simpa [hne.symm] using hy.edge_mem



namespace Graph

lemma IsPathGraph.konig (h : G.IsPathGraph) : τ(G) = ν(G) := by
  have := h.finite
  obtain ⟨P, hP, rfl⟩ := h
  refine matchingNumber_le_coverNumber.antisymm' <| le_trans (b := ↑(V(P).ncard / 2)) ?_ ?_
  · rw [← pathCover_ncard hP.nodup,
    (this.vertexSet_finite.subset <| by simpa using P.pathCover_subset).cast_ncard_eq]
    exact (pathCover_isCover hP.isWalk.wellFormed).le_encard
  sorry

lemma IsCycleGraph.konig (hB : G.Bipartite) (h : G.IsCycleGraph) : τ(G) = ν(G) := by
  sorry

/-!
### König's Matching Theorem
Source: Romeo Rizzi (2000) [cite: 2]

Theorem: Let G be a bipartite graph. Then ν(G) = τ(G).

Proof:
Let G be a minimal counterexample. Then G is connected, is not a circuit, nor a path. [cite: 14]
So, G has a node of degree at least 3. Let u be such a node and v one of its neighbors. [cite: 15]

Case 1: If ν(G \ v) < ν(G). [cite: 16]
By minimality, G \ v has a cover W' with |W'| < ν(G). [cite: 16]
Hence, W' ∪ {v} is a cover of G with cardinality ν(G) at most. [cite: 17]

Case 2: Assume there exists a maximum matching M of G having no edge incident at v. [cite: 18]
Let f be an edge of G \ M incident at u but not at v. [cite: 18]
Let W' be a cover of G \ f with |W'| = ν(G). [cite: 22]
Since no edge of M is incident at v, it follows that W' does not contain v. [cite: 22]
So W' contains u and is a cover of G. [cite: 22]
-/
theorem Konig'sTheorem [H.Finite] (hB : H.Bipartite) : τ(H) = ν(H) := by
  refine of_not_exists_minimal (P := fun H ↦ τ(H) = ν(H)) fun G hle _ hMin ↦ ?_
  push_neg at hMin
  replace hB := hB.of_le hle
  have hcon : G.Connected := by
    /- Otherwise, by def of `Connected`, there is a strictly smaller component of `G`.
    `τ` and `ν` are additive over the components so at least one component must have `τ` or `ν`
    different.
    That component is a smaller counterexample to the theorem, contradicting minimality.-/
    sorry
  obtain ⟨u, hu, hdegu⟩ : ∃ u ∈ V(G), 3 ≤ G.degree u := by
    /- Otherwise, by `isPathGraph_or_isCycleGraph_of_maxDegreeLE`, `G` would be a path or cycle,
    By lemmas above, any path graph or cycle graph has `τ = ν`, contradicting `τ ≠ ν` assumption.-/
    sorry
  obtain ⟨e, v, huv⟩ := G.degree_ne_zero_iff_inc (v := u) |>.mp (by omega)

  -- have hlt := G.coverNumber_le_matchingNumber.lt_of_ne hne
  sorry

end Graph
