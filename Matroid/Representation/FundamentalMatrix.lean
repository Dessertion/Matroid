import Mathlib.LinearAlgebra.LinearIndependent
import Matroid.Simple
import Matroid.Representation.StandardRep
import Matroid.Binary.Crossing
import Matroid.Order.Quotient
import Mathlib.Data.Finsupp.Indicator

variable {α β W W' 𝔽 R : Type*} {e f x : α} {I E B X Y : Set α} {M : Matroid α} [DivisionRing 𝔽]
[DivisionRing R]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W'] [M.Finitary]

-- theorem Finsupp.support_indicator_eq {ι α : Type*} [Zero α] (s : Finset ι)
--   (f : (i : ι) → i ∈ s → α) :
--     ((Finsupp.indicator s f).support : Set ι) = {i ∈ s | f i }

open Function Set Submodule FiniteDimensional BigOperators Matrix Set.Notation

namespace Matroid

/-- The intersection of `M.fundCircuit e B` with `B` as a `Finset B` in a finitary matroid. -/
noncomputable def Base.coords (hB : M.Base B) (e : α) : Finset B :=
  Finite.toFinset (s := (B ↓∩ M.fundCircuit e B))
  (by
    refine Finite.preimage Subtype.val_injective.injOn ?_
    by_cases heB : e ∈ B
    · rw [fundCircuit_eq_of_mem heB]
      simp
    by_cases heE : e ∈ M.E
    · exact (hB.fundCircuit_circuit heE heB).finite
    rw [fundCircuit_eq_of_not_mem_ground heE]
    simp )

lemma Base.coords_of_mem (hB : M.Base B) (he : e ∈ B) :
    hB.coords e = {⟨e, he⟩} := by
  ext ⟨x, hx⟩
  simp [coords, hB.subset_ground he, fundCircuit_eq_of_mem he]

lemma Base.coords_of_not_mem_ground (hB : M.Base B) (heE : e ∉ M.E) : hB.coords e = ∅ := by
  suffices ∀ a ∈ B, a ≠ e by
    simpa [coords, fundCircuit_eq_of_not_mem_ground heE, eq_empty_iff_forall_not_mem]
  rintro x hxB rfl
  exact heE <| hB.subset_ground hxB

lemma Base.coords_toSet (hB : M.Base B) : (hB.coords e : Set B) = B ↓∩ (M.fundCircuit e B) := by
  simp [coords]

lemma Base.fundCircuit_eq_insert_map [DecidableEq α] (hB : M.Base B) :
    M.fundCircuit e B = insert e ((hB.coords e).map (Embedding.setSubtype B)) := by
  by_cases heB : e ∈ B
  · simp [fundCircuit_eq_of_mem heB, Set.ext_iff, coords]
  simp [hB.coords_toSet, inter_comm B, ← fundCircuit_diff_eq_inter _ heB,
    insert_eq_of_mem (mem_fundCircuit ..)]

/-- The column of the `B`-fundamental matrix of `M` corresponding to `e`, as a `Finsupp`. -/
noncomputable def Base.fundCoord (hB : M.Base B) (R : Type*) [Semiring R] (e : α) :
    B →₀ R :=
  Finsupp.indicator (hB.coords e) (fun _ _ ↦ 1)

variable {R : Type*} [DivisionRing R]

lemma Base.fundCoord_of_mem (hB : M.Base B) (he : e ∈ B) :
    hB.fundCoord R e = Finsupp.single ⟨e, he⟩ 1 := by
  rw [fundCoord, coords_of_mem hB he, Finsupp.single_eq_indicator]

@[simp] lemma Base.fundCoord_mem (hB : M.Base B) (e : B) : hB.fundCoord R e = Finsupp.single e 1 :=
  hB.fundCoord_of_mem e.2

lemma Base.fundCoord_of_not_mem_ground (hB : M.Base B) (he : e ∉ M.E) :
    hB.fundCoord R e = 0 := by
  rw [fundCoord, coords_of_not_mem_ground hB he]
  rfl

lemma Base.support_fundCoord_subset (hB : M.Base B) : support (hB.fundCoord R) ⊆ M.E :=
  support_subset_iff'.2 fun _ ↦ hB.fundCoord_of_not_mem_ground

lemma Base.fundCoord_support (hB : M.Base B) :
    (↑) '' ((hB.fundCoord R e).support : Set B) = (M.fundCircuit e B) ∩ B := by
  simp [Set.ext_iff, fundCoord, Base.coords, Finsupp.indicator]

lemma Base.fundCoord_base (hB : M.Base B) : (Matroid.ofFun R M.E (hB.fundCoord R)).Base B :=
  Finsupp.basisSingleOne.ofFun_base (by simp) hB.subset_ground

lemma Base.fundCoord_eq_linearCombination (hB : M.Base B) :
    hB.fundCoord R e = Finsupp.linearCombination R (Finsupp.single · 1) (hB.fundCoord R e) := by
  rw [Base.fundCoord, Finsupp.linearCombination_apply, Finsupp.indicator_eq_sum_single]
  simp

lemma Base.fundCoord_finitaryBase (hB : M.Base B) (R : Type*) [DivisionRing R] :
    (Matroid.repOfFun R M.E (hB.fundCoord R)).FinitaryBase := by
  intro e
  simp only [repOfFun_coeFun_eq]
  rw [indicator_of_mem (hB.subset_ground e.2), fundCoord_of_mem]

lemma funCoord_fundCircuit (hB : M.Base B) (heB : e ∉ B) (heE : e ∈ M.E) :
    (Matroid.ofFun R M.E (hB.fundCoord R)).Circuit (M.fundCircuit e B) := by
  classical
  convert (hB.fundCoord_finitaryBase R).circuit_insert_support heB heE using 1
  rw [hB.fundCircuit_eq_insert_map]
  simp only [Finset.coe_insert, Finset.coe_map, Embedding.setSubtype_apply, repOfFun_coeFun_eq]
  convert rfl
  ext x
  simp only [Finsupp.mem_support_iff, ne_eq]
  rw [Set.indicator_of_mem heE]
  rw [Base.fundCoord]
  simp


  -- simp [hB.coords_toSet, hB.fundCoord_support]




  -- classical
  -- simp_rw [hB.fundCircuit_eq_insert_map heE, Finset.coe_insert, Finset.coe_map,
  --   Embedding.setSubtype_apply]
  -- refine Indep.insert_circuit_of_forall ?_ ?_ ?_ ?_
  -- · exact hB.fundCoord_base.indep.subset (by simp)
  -- · simp [heB]
  -- · rw [hB.coords_toSet heE, Matroid.ofFun_closure_eq hB.support_fundCoord_subset,
  --     mem_inter_iff, and_iff_left heE, Subtype.image_preimage_coe, mem_preimage, SetLike.mem_coe,
  --     Finsupp.mem_span_image_iff_linearCombination, hB.fundCoord_eq_linearCombination]
  --   refine ⟨(hB.fundCoord R e).embDomain (Embedding.setSubtype B), ?_, ?_⟩
  --   · simp only [Base.fundCoord, Finsupp.mem_supported, Finsupp.support_embDomain, Finset.coe_map,
  --       Embedding.setSubtype_apply, subset_inter_iff, image_subset_iff, Subtype.coe_preimage_self,
  --       subset_univ, true_and]
  --     refine (Finsupp.support_indicator_subset ..).trans ?_
  --     rw [hB.coords_toSet heE]
  --   simp only [Finsupp.linearCombination_embDomain]
  --   convert rfl with _ x
  --   simp
  -- simp
  -- rw [fundCircuit_eq_sInter (by rwa [hB.closure_eq])]
  -- refine Indep.insert_circuit_of_forall ?_ ?_ ?_ ?_
  -- · exact hB.fundCoord_base.indep.subset inter_subset_left
  -- · simp [heB]
  -- · rw [ofFun_closure_eq_of_subset_ground (inter_subset_left.trans hB.subset_ground),
  --     mem_inter_iff, and_iff_left heE]
  --   simp
  --   rw [hB.fundCoord_eq_linearCombination, Finsupp.mem_span_image_iff_linearCombination]
  --   use (hB.fundCoord R e).embDomain (Embedding.setSubtype B)
  --   rw [Base.fundCoord]
  --   simp






  -- have := (Finsupp.basisSingleOne (ι := B) (R := R)).ofFun_base (E := M.E) (v := hB.fundCoord R)
  -- refine Indep.base_of_ground_subset_closure ?_ ?_
  -- · rw [ofFun_indep_iff, and_iff_left hB.subset_ground]
  --   convert (Finsupp.basisSingleOne (ι := B) (R := R)).linearIndependent
  --   ext ⟨i, hi⟩ ⟨j, hj⟩
  --   simp [hB.fundCoord_of_mem hi]
  -- rw [ofFun_ground_eq, ofFun_closure_eq (hB.support_fundCoord_subset)]
