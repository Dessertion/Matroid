import Matroid.Extension.ProjectBy
import Matroid.ForMathlib.FinDiff

variable {α : Type*} {M : Matroid α} {E I B C X Y : Set α} {k : ℕ∞} {e f : α}

namespace Matroid

open Set


section IsFreeBase

variable {B B' : Set α}

/-- A free base is one where exchanging any two elements gives a base. -/
@[mk_iff]
structure IsFreeBase (M : Matroid α) (B : Set α) : Prop where
  isBase : M.IsBase B
  isBase_of_exchange : ∀ B' ⊆ M.E, B'.IsExchange B → M.IsBase B'

lemma IsFreeBase.isBase_insert_diff_singleton (h : M.IsFreeBase B) (he : e ∈ B) (hf : f ∈ M.E \ B) :
    M.IsBase (insert f (B \ {e})) :=
  h.isBase_of_exchange _ (by grind [h.isBase.subset_ground]) (isExchange_diff_insert he hf.2).symm

lemma IsFreeBase.compl_dual (hB : M.IsFreeBase B) : M✶.IsFreeBase (M.E \ B) := by
  refine ⟨hB.isBase.compl_isBase_dual, fun B' hB' hB'ex ↦ ?_⟩
  have h1 := (isExchange_diff_right_comm hB' hB.isBase.subset_ground).1 hB'ex
  have h2 := (hB.isBase_of_exchange _ diff_subset h1).compl_isBase_dual
  rwa [diff_diff_cancel_left (by simpa)] at h2

lemma isFreeBase_dual_iff (hB : B ⊆ M.E) : M✶.IsFreeBase B ↔ M.IsFreeBase (M.E \ B) := by
  refine ⟨fun h ↦ by simpa using h.compl_dual, fun h ↦ ?_⟩
  rw [← diff_diff_cancel_left hB]
  exact h.compl_dual

lemma IsFreeBase.indep_of_ssubset_insert (hB : M.IsFreeBase B) (hI : I ⊂ insert e B)
    (he : e ∈ M.E := by aesop_mat) : M.Indep I := by
  by_cases! he : e ∉ (I \ B)
  · exact hB.isBase.indep.subset <| by grind
  obtain ⟨f, hf⟩ := exists_of_ssubset hI
  refine (hB.isBase_insert_diff_singleton (e := f) (f := e) ?_ ?_).indep.subset ?_ <;>
  grind

end IsFreeBase

lemma IsBase.isBase_of_indep_of_finDiff (hB : M.IsBase B) (hI : M.Indep I) (hBI : FinDiff B I) :
    M.IsBase I := by
  obtain ⟨B', hB', hIB'⟩ := hI.exists_isBase_superset
  have hfin' : FinDiff B B' := by
    rw [finDiff_iff, hB'.encard_diff_comm hB, and_iff_left rfl]
    exact hBI.diff_finite.subset (diff_subset_diff_right hIB')
  rwa [(hBI.symm.trans hfin').eq_of_subset hIB']

lemma IsBase.isBase_of_spanning_of_finDiff {S : Set α} (hB : M.IsBase B) (hS : M.Spanning S)
    (hBS : FinDiff B S) : M.IsBase S := by
  rw [← M.dual_dual, dual_isBase_iff]
  exact hB.compl_isBase_dual.isBase_of_indep_of_finDiff hS.compl_coindep <|
    hBS.diff_right hB.subset_ground hS.subset_ground

lemma IsBase.eq_of_isBase_finDiff_finDiff_subset {Y : Set α} (hB : M.IsBase B) (hBX : B.FinDiff X)
    (hC : M.IsBase C) (hCY : C.FinDiff Y) (hXY : X ⊆ Y) : X = Y := by
  by_cases hss : Y ⊆ X ∪ C
  · have hd' := hCY.diff_diff (P := Y \ X) (by grind) diff_subset
    rw [diff_diff_cancel_left hXY] at hd'
    have h' := hd'.trans hBX.symm
    have hb := (hB.isBase_of_indep_of_finDiff (hC.indep.subset diff_subset) h'.symm)
    grind [hb.eq_of_subset_isBase hC diff_subset]
  obtain ⟨e, hecY, heXC⟩ := not_subset.1 hss
  obtain ⟨f, hf⟩ := hCY.diff_nonempty_of_nonempty ⟨e, by grind⟩
  have hlt : ((insert f (Y \ {e})) \ (X ∪ C)).encard < (Y \ (X ∪ C)).encard := by
    have hss : (insert f (Y \ {e})) \ (X ∪ C) ⊂ Y \ (X ∪ C) :=
      ssubset_iff_exists.2 ⟨by grind, e, by grind⟩
    exact ((hCY.symm.diff_finite.subset (by grind)).subset hss.subset).encard_lt_encard hss
  have hwin := hB.eq_of_isBase_finDiff_finDiff_subset (Y := insert f (Y \ {e})) hBX hC ?_ (by grind)
  · grind
  exact hCY.trans_exchange <| isExchange_diff_insert hecY hf.2
termination_by (Y \ (X ∪ C)).encard

/-- The collection of sets that are `FinDiff` of some base is an antichain.
(for a finite-rank matroid `M`, these are the sets whos cardinality is the rank of `M`.)-/
lemma isAntichain_setOf_finDiff_isBase (M : Matroid α) :
    IsAntichain (· ⊆ ·) {X | ∃ B, M.IsBase B ∧ B.FinDiff X} :=
  fun _ ⟨_, hB, hBX⟩ _ ⟨_, hC, hCY⟩ hne hXY ↦ hne <|
    hB.eq_of_isBase_finDiff_finDiff_subset hBX hC hCY hXY

lemma IsBase.finDiff_iff_encard_eq_eRank [M.RankFinite] (hB : M.IsBase B) :
    FinDiff B X ↔ X.encard = M.eRank := by
  rw [hB.finite.finDiff_iff_encard_eq, eq_comm, hB.encard_eq_eRank]
