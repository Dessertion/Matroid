import Matroid.Extremal.Covers

set_option linter.style.longLine false

variable {α : Type*} {M N M' : Matroid α} {I F X Y F' F₀ F₁ F₂ P L H H₁ H₂ H' B C D K : Set α}
  {e f : α} {l r : ℕ} {a k : ℕ∞} {T : Set (Set α)} {ι : Type*} {i j : ι}
  {P P' : Matroid α → Set α → Prop}

open Set
namespace Matroid

section defs

--Ask about -1. Do we need M.RankPos?

def IsThick (M : Matroid α) (d : ℕ∞) : Prop := d ≤ M.coverNumber (fun M X ↦ M.eRk X ≤ (M.eRank - 1))

def IsThick_set (M : Matroid α) (X : Set α ) (d : ℕ∞) : Prop :=
    (M ↾ X).IsThick d

lemma IsThick_set_iff (M : Matroid α) (X : Set α ) (d : ℕ∞) :
    M.IsThick_set X d ↔ d ≤ (M ↾ X).coverNumber (fun M X ↦ M.eRk X ≤ (M.eRk X - 1)) := by
  sorry

lemma IsThick_two [M.Nonempty] (M : Matroid α) : M.IsThick 2 := by
  obtain ht | ⟨T, hT, hTe ⟩ := exists_cover M (fun M X ↦ M.eRk X ≤ (M.eRank - 1))
  · unfold IsThick
    rw [ ht]
    simp
  unfold IsThick
  rw [←hTe]
  have : M.IsRankCover (M.eRank - 1) T := by sorry
  --( IsRankCover_iff_IsCover M (M.eRank - 1) T ).2 hT
  --IsRankCover_two
  sorry


end defs
