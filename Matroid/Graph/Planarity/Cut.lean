import Mathlib.Analysis.InnerProductSpace.PiL2 -- inefficient import
import Mathlib.Topology.UniformSpace.Path -- inefficient import
import Mathlib.Topology.Separation.Connected -- inefficient import
import Mathlib.Topology.LocallyConstant.Basic -- inefficient import

namespace Topology

open Set Function
variable {α : Type*} [TopologicalSpace α] {S T : Set α} {a b c x y z : α}

def Bound (S : Set α) (x a : α) : Prop := a ∈ frontier (connectedComponentIn Sᶜ x)

lemma bound_of_mem (ha : a ∈ S) (h : a ∈ closure (connectedComponentIn Sᶜ x)) : Bound S x a :=
  ⟨h, fun h' ↦ connectedComponentIn_subset _ _ (interior_subset h') ha⟩

def Cut (S : Set α) : Set α := closure (interior S) ∩ (interior (closure S))ᶜ

-- lemma cut_nonempty [PreconnectedSpace α] (h : IsOpen (closure (interior S) ∪
--     (interior (closure S))ᶜ)) (hine : (interior S).Nonempty) (hcne : (closure S)ᶜ.Nonempty) :
--     (Cut S).Nonempty := by
--   let ic := closure (interior S)
--   let ec := (interior (closure S))ᶜ
--   rw [Cut, ← not_disjoint_iff_nonempty_inter]
--   change ¬ Disjoint ic ec

--   replace hcne : ic ≠ univ := by
--     rw [ne_univ_iff_exists_notMem]
--     use hcne.some, (hcne.some_mem <| closure_mono interior_subset ·)
--   replace hine : ic ≠ ∅ := by
--     rw [← nonempty_iff_ne_empty]
--     use hine.some, subset_closure hine.some_mem
--   have := (isClopen_iff (s := ic)).not.mpr (by simp [hine, hcne])
--   contrapose! this
--   use isClosed_closure
--   convert (isOpen_interior (s := closure S)).isClosed_compl.union h.isClosed_compl |>.isOpen_compl
--   tauto_set

lemma IsOpen.cut_nonempty [PreconnectedSpace α] (h : IsOpen S) (hine : S.Nonempty)
    (hcne : (closure S)ᶜ.Nonempty) : (Cut S).Nonempty := by
  rw [Cut, ← not_disjoint_iff_nonempty_inter, h.interior_eq, disjoint_compl_right_iff_subset,
    subset_interior_iff_isOpen]
  rintro ho
  replace ho : IsClopen (closure S) := ⟨isClosed_closure, ho⟩
  rw [isClopen_iff, eq_empty_iff_forall_notMem, eq_univ_iff_forall] at ho
  obtain he | hu := ho
  · exact he hine.some (subset_closure hine.some_mem)
  exact hcne.some_mem <| hu hcne.some

lemma segment_union_eq_segment {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {x y z : E}
    (hz : z ∈ segment 𝕜 x y) : segment 𝕜 x z ∪ segment 𝕜 z y = segment 𝕜 x y := by
  simp only [segment_eq_image, mem_image, mem_Icc] at hz ⊢
  obtain ⟨t, ht, rfl⟩ := hz
  suffices (fun a ↦ (1 - a * t) • x + (a * t) • y) '' Icc 0 1 ∪
    (fun a ↦ (1 - (a * (1 - t) + t)) • x + (a * (1 - t) + t) • y) '' Icc 0 1 =
    (fun (θ : 𝕜) ↦ (1 - θ) • x + θ • y) '' Icc 0 1 by
    convert this using 3
    · simp only [smul_add, smul_smul, ← add_assoc, ← add_smul]
      ring_nf
    · simp only [smul_add, smul_smul, add_assoc, ← add_smul]
      ring_nf
  rw [(show (fun a ↦ (1 - a * t) • x + (a * t) • y) = (fun (θ : 𝕜) ↦ (1 - θ) • x + θ • y) ∘
    (· * t) from rfl), image_comp, image_mul_right_Icc (by positivity) ht.1, zero_mul, one_mul,
    (show (fun a ↦ (1 - (a * (1 - t) + t)) • x + (a * (1 - t) + t) • y) = (fun (θ : 𝕜) ↦
    (1 - θ) • x + θ • y) ∘ (· + t) ∘ (· * (1 - t)) from rfl), image_comp, image_comp,
    image_mul_right_Icc (by positivity) (by linarith), zero_mul, one_mul,
    image_add_const_Icc, zero_add, sub_add_cancel, ← image_union]
  congr
  exact Icc_union_Icc_eq_Icc ht.1 ht.2


end Topology
