import Matroid.Extremal.Covers

set_option linter.style.longLine false

variable {α : Type*} {M N M' : Matroid α} {I F X Y F' F₀ F₁ F₂ P L H H₁ H₂ H' B C D K : Set α}
  {e f : α} {l r : ℕ} {a k d : ℕ∞} {T : Set (Set α)} {ι : Type*} {i j : ι}
  {P P' : Matroid α → Set α → Prop}

open Set
namespace Matroid

section defs

def IsThick (M : Matroid α) (d : ℕ∞) : Prop := d ≤ M.coverNumber Matroid.Nonspanning

lemma IsThick_iff (M : Matroid α) (d : ℕ∞) :
    M.IsThick d ↔ d ≤ M.coverNumber Matroid.Nonspanning := Eq.to_iff rfl

lemma IsThick_iff' (M : Matroid α) (d : ℕ∞) :
    M.IsThick d ↔ ∀ T, M.IsCover Matroid.Nonspanning T → d ≤ T.encard := by
  refine ⟨?_, ?_ ⟩
  · intro h T hT

    sorry
  sorry


def IsThick_set (M : Matroid α) (X : Set α ) (d : ℕ∞) : Prop :=
    (M ↾ X).IsThick d

lemma IsThick_set_iff (M : Matroid α) (X : Set α ) (d : ℕ∞) :
    M.IsThick_set X d ↔ d ≤ (M ↾ X).coverNumber Matroid.Nonspanning := by
  sorry

lemma IsThick_two (M : Matroid α) [M.Nonempty] : M.IsThick 2 := by
  rw [M.IsThick_iff 2]
  obtain ht | ⟨T, hT, hTe ⟩ := exists_cover M Matroid.Nonspanning
  · rw [ ht]
    simp only [le_top]
  rw [← hTe ]
  by_contra hc
  obtain ⟨X, hX ⟩ := encard_eq_one.mp ((ENat.one_le_iff_ne_zero.mpr (encard_ne_zero.mpr
    ( hT.nonempty ))).antisymm' (Order.le_of_lt_succ (Std.not_le.mp hc ) ) )
  have hc1 : M.Spanning X := by
    rw [← sUnion_singleton (s := X), ←hX, hT.sUnion_eq]
    refine ⟨ by simp only [closure_ground], by simp only [subset_refl] ⟩
  exact Ne.elim (fun a ↦ (hT.pProp X ( by rw [hX]; exact mem_singleton X )).not_spanning  hc1) hTe

lemma IsThick.mono {d' : ℕ∞} (hTd : M.IsThick d ) (hd : d' ≤ d ) : M.IsThick d' := by sorry


lemma IsThick_set.Minor_mon (hTXd : M.IsThick_set X d) (hNM : N ≤m M ) ( hX : X ⊆ N.E )
    (hXne : (M ↾ X ).Nonempty) :
    N.IsThick_set X d := by
  rw [N.IsThick_set_iff X d]
  obtain ⟨C, D, hC, hD, hDC, hrw ⟩ := hNM.exists_contract_indep_delete_coindep
  have hDX : Disjoint D X := by grind
  have hCX : Disjoint C X := by grind
  have hg3 : (C ∩ M.closure X) ⊆ (M ↾ (X ∪ (C ∩ M.closure X))).E := by grind
  have hne : ((M ↾ (X ∪ (C ∩ M.closure X))) ／ (C ∩ M.closure X)).Nonempty := by
    refine (ground_nonempty_iff ((M ↾ (X ∪ C ∩ M.closure X)) ／ (C ∩ M.closure X))).mp ?_
    simp only [contract_ground, restrict_ground_eq, union_diff_right]
    have : (X \ C).Nonempty := by
      rw [ Disjoint.sdiff_eq_right hCX ]
      rwa [←(M ↾ X).ground_nonempty_iff, restrict_ground_eq] at hXne
    refine nonempty_of_not_subset ?_
    have : ¬X ⊆ C := by
      exact not_subset.mpr this
    grind
  -- Peter?
  have hP : (M ／ C ↾ X) = (M ／ (C ∩ M.closure X) ↾ X) := by sorry
  have hCX' : Disjoint (C ∩ M.closure X) X := by grind
  grw [hrw, delete_restrict_eq_restrict (M ／ C) hDX, hP,
    M.contract_restrict_eq_restrict_contract hCX',
    ←NonSpanningNumber_contract hg3 hne, ← NonSpanningNumber_set_closure (inter_subset_right)
    (by grind) ]
  exact (IsThick_set_iff M X d).mp hTXd





end defs
