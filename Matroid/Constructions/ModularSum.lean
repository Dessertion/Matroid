import Matroid.Modular.Flat
import Matroid.Axioms.Flat

variable {α ι : Type*} {M N : Matroid α} {X Y C F F' T : Set α} {e f g : α}

open Set

namespace Matroid

@[pp_nodot]
structure SumFlat (M N : Matroid α) (F : Set α) : Prop where
  isFlat_left : M.IsFlat (F ∩ M.E)
  isFlat_right : N.IsFlat (F ∩ N.E)
  subset_union : F ⊆ M.E ∪ N.E

lemma sumFlat_ground (M N : Matroid α) : SumFlat M N (M.E ∪ N.E) := by
  refine ⟨?_, ?_, rfl.subset⟩
  · rw [inter_eq_self_of_subset_right subset_union_left]
    exact M.ground_isFlat
  rw [inter_eq_self_of_subset_right subset_union_right]
  exact N.ground_isFlat

lemma sumFlat_iInter [Nonempty ι] (F : ι → Set α) (hFs : ∀ i, SumFlat M N (F i)) :
    SumFlat M N <| (⋂ i, F i) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [iInter_inter]
    exact IsFlat.iInter fun i ↦ (hFs i).isFlat_left
  · rw [iInter_inter]
    exact IsFlat.iInter fun i ↦ (hFs i).isFlat_right
  sorry


lemma SumFlat.inter (hF : SumFlat M N F) (hF' : SumFlat M N F') :
    SumFlat M N (F ∩ F') := sorry

@[simp]
lemma sumFlat_closure_union_closure (X Y : Set α) : SumFlat M N (M.closure X ∪ N.closure Y) := sorry

lemma SumFlat.foo_left (hF : SumFlat M N F) (he : e ∈ M.E) (heF : e ∉ F) :
    ∃! F', SumFlat M N F' ∧ e ∈ F' ∧ Minimal (fun X ↦ F ⊂ X ∧ SumFlat M N X) F' := by
  refine ⟨M.closure (insert e F) ∪ N.closure ((F ∩ N.E) ∪ M.closure (F ∩ M.E ∩ N.E)), ⟨?_, ?_⟩, ?_⟩

lemma SumFlat.foo (hF : SumFlat M N F) (he : e ∈ M.E ∪ N.E) (heF : e ∉ F) :
    ∃! F', SumFlat M N F' ∧ e ∈ F' ∧ Minimal (fun X ↦ F ⊂ X ∧ SumFlat M N X) F' := by
  sorry

    -- rw [inter_assoc, inter_eq_self_of_subset_right subset_union_left]
    -- have := IsFlat.iInter_inter_ground (M := M) (Fs := fun (F : Fs) ↦ F.1 ∩ M.E)
    --   (fun F ↦ (hFs F.1 F.2).isFlat_left)
    -- simp only [iInter_coe_set] at this
    -- rw [biInter_inter] at this
