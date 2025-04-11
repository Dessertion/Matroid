/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finite.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.ZMod.Defs

/-!
# Finite Cardinality Functions

## Main Definitions

* `ENat.card α` is the cardinality of `α` as an  extended natural number.
  If `α` is infinite, `ENat.card α = ⊤`.
* `Nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `Nat.card α = 0`.
-/

assert_not_exists Field

open Function

noncomputable section

variable {α β : Type*}

universe u v

variable {α β : Type*}

section ENatLemmas

variable {a b m n : ℕ∞}

def ENat.recTopZeroCoe {C : ℕ∞ → Sort*} (top : C ⊤) (zero : C 0) (coe : (a : ℕ) → C ↑(a + 1))
    (n : ℕ∞) : C n :=
  ENat.recTopCoe (n := n) top fun a ↦ a.recAux zero fun b _ ↦ coe b

lemma ENat.le_one_iff : a ≤ 1 ↔ (a = 0) ∨ (a = 1) := by
  cases a using ENat.recTopCoe with
  | top => simp
  | coe a => simpa using Nat.le_one_iff_eq_zero_or_eq_one

lemma ENat.natCast_lt_add_right_iff (a : ℕ) {b : ℕ∞} : a < a + b ↔ b ≠ 0 := by
  cases b using ENat.recTopCoe with
  | top => simp
  | coe b => simp [← Nat.cast_add, Nat.ne_zero_iff_zero_lt]

lemma ENat.natCast_lt_add_left_iff (a : ℕ) {b : ℕ∞} : a < b + a ↔ b ≠ 0 := by
  rw [add_comm, ENat.natCast_lt_add_right_iff]

@[simp]
lemma ENat.lt_add_right_iff (a b : ℕ∞) : a < a + b ↔ a ≠ ⊤ ∧ b ≠ 0 := by
  cases a using ENat.recTopCoe with
  | top => simp
  | coe a => simp [ENat.natCast_lt_add_right_iff]

@[simp]
lemma ENat.lt_add_left_iff (a b : ℕ∞) : a < b + a ↔ a ≠ ⊤ ∧ b ≠ 0 := by
  simp [add_comm]

lemma ENat.coe_lt_iff {a : ℕ} {b : ℕ∞} : a < b ↔ a + 1 ≤ b := by
  cases b using ENat.recTopCoe with
  | top => simp
  | coe b => norm_cast

lemma ENat.sSup_eq_top_iff {s : Set ℕ∞} : sSup s = ⊤ ↔ ∀ n : ℕ, ∃ x ∈ s, n ≤ x := by
  refine sSup_eq_top.trans ⟨fun h n ↦ ?_, fun h b hb ↦ ?_⟩
  · obtain ⟨a, has, hba⟩ := h n (by simp)
    exact ⟨_, has, hba.le⟩
  lift b to ℕ using hb.ne
  obtain ⟨x, hx, hbx⟩ := h (b+1)
  exact ⟨x, hx, ENat.coe_lt_iff.2 hbx⟩

@[simp]
lemma ENat.mul_eq_zero {m n : ℕ∞} : m * n = 0 ↔ m = 0 ∨ n = 0 := by
  wlog hmn : m ≤ n with aux
  · rw [mul_comm, aux (not_le.1 hmn).le, or_comm]
  cases n using ENat.recTopCoe with
  | top => obtain h | h := eq_or_ne m 0 <;> simp [h]
  | coe n =>
  lift m to ℕ using (hmn.trans_lt (by simp)).ne
  norm_cast
  simp

-- @[simp]
-- protected lemma ENat.mul_eq_one {m n : ℕ∞} : m * n = 1 ↔ m = 1 ∧ n = 1 := by
--   wlog hle : n ≤ m with aux
--   · rw [mul_comm, aux (not_le.1 hle).le, and_comm]
--   cases m using ENat.recTopCoe with
--   | top =>
--     cases n using ENat.recTopCoe with
--     | top => simp
--     | coe n =>
--     simp only [top_ne_one, Nat.cast_eq_one, false_and, iff_false]
--     obtain rfl | n := n <;> simp
--   | coe m =>
--   lift n to ℕ using (hle.trans_lt (by simp)).ne
--   norm_cast
--   simp

lemma ENat.toNat_mul (m n : ℕ∞) : (m * n).toNat = m.toNat * n.toNat := by
  cases m using ENat.recTopCoe with
  | top => simp +contextual [or_iff_not_imp_left]
  | coe m =>
  cases n using ENat.recTopCoe with
  | top => simp +contextual [or_iff_not_imp_left]
  | coe n =>
  norm_cast

@[simp]
lemma ENat.toNat_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ∞) :
    (∏ i ∈ s, f i).toNat = ∏ i ∈ s, (f i).toNat := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hxs ih => rw [Finset.prod_insert hxs, ENat.toNat_mul, Finset.prod_insert hxs, ih]

instance : NoZeroDivisors ℕ∞ where
  eq_zero_or_eq_zero_of_mul_eq_zero := ENat.mul_eq_zero.1

instance : OrderedCommMonoid ℕ∞ := CanonicallyOrderedAdd.toOrderedCommMonoid

-- def ENat.pow' (m : ℕ∞) : ℕ∞ → ℕ∞ := ENat.recTopCoe (if m ≤ 1 then m else ⊤) (m ^ ·)
-- -- | m, (n : ℕ) => m ^ n
-- -- | m, ⊤ => if m ≤ 1 then m else ⊤

-- instance : Pow ℕ∞ ℕ∞ where
--   pow := ENat.pow'

-- protected lemma ENat.pow_top (ha : 1 < a) : a ^ (⊤ : ℕ∞) = ⊤ := by
--   change ENat.pow' _ _ = _
--   simp [ENat.pow', ha.not_le]

-- protected lemma ENat.pow_top_eq_self (ha : a ≤ 1) : a ^ (⊤ : ℕ∞) = a := by
--   change ENat.pow' _ _ = _
--   simp [ENat.pow', ha.not_lt]

-- protected lemma ENat.pow_top_eq_ite (a : ℕ∞) : a ^ (⊤ : ℕ∞) =
--     if a = 0 then 0 else if a = 1 then 1 else ⊤ := by
--   split_ifs with h₁ h₂
--   · simp [h₁, ENat.pow_top_eq_self]
--   · simp [h₂, ENat.pow_top_eq_self]
--   rw [ENat.pow_top]
--   simp [← not_le, ENat.le_one_iff, *]

-- @[simp] protected lemma ENat.top_pow_top : (⊤ : ℕ∞) ^ (⊤ : ℕ∞) = ⊤ := rfl

-- @[simp] protected lemma ENat.zero_pow_top : (0 : ℕ∞) ^ (⊤ : ℕ∞) = 0 := rfl

-- @[simp]
-- lemma ENat.pow_natCast (a : ℕ∞) (b : ℕ) : a ^ (b : ℕ∞) = a ^ b := rfl

-- @[simp]
-- lemma ENat.natCast_pow_natCast (a b : ℕ) : (a : ℕ∞) ^ (b : ℕ∞) = (a ^ b : ℕ) := rfl

-- @[simp]
-- protected lemma ENat.one_pow (a : ℕ∞) : (1 : ℕ∞) ^ a = 1 := by
--   cases a using ENat.recTopCoe with
--   | top => rw [ENat.pow_top_eq_self rfl.le]
--   | coe a => simp [ENat.pow_natCast]

-- protected lemma ENat.zero_pow_eq (a : ℕ∞) : (0 : ℕ∞) ^ a = if a = 0 then 1 else 0 := by
--   cases a using ENat.recTopCoe with
--   | top => simp [ENat.pow_top_eq_self (a := 0) (by simp)]
--   | coe a => simp [ENat.pow_natCast, zero_pow_eq]

-- @[simp]
-- protected lemma ENat.pow_eq_zero : a ^ b = 0 ↔ a = 0 ∧ b ≠ 0 := by
--   cases b using ENat.recTopCoe with
--   | top =>
--     obtain hle | hlt := le_or_lt a 1
--     · obtain rfl | rfl := ENat.le_one_iff.1 hle <;> simp [ENat.zero_pow_eq]
--     simp [ENat.pow_top hlt, show a ≠ 0 by rintro rfl; simp at hlt]
--   | coe b => simp [pow_natCast]

-- @[simp]
-- protected lemma ENat.pow_one (a : ℕ∞) : a ^ 1 = a := by
--   cases a using ENat.recTopCoe with
--   | top => simp
--   | coe a => simp

-- @[simp]
-- protected lemma ENat.pow_zero (a : ℕ∞) : a ^ (0 : ℕ∞) = 1 := by
--   cases a using ENat.recTopCoe with
--   | top => rfl
--   | coe a => rfl

-- protected lemma ENat.pow_add (a b b' : ℕ∞) : a ^ b * a ^ b' = a ^ (b + b') := by
--   wlog hle : b ≤ b' generalizing b b' with aux
--   · rw [mul_comm, aux _ _ (not_le.1 hle).le, add_comm]
--   cases b' using ENat.recTopCoe with
--   | top =>
--     obtain ha | ha := le_or_lt a 1
--     · obtain rfl | rfl := ENat.le_one_iff.1 ha <;> simp [ENat.zero_pow_eq]
--     simp [ENat.pow_top ha, mul_top, show a ≠ 0 by rintro rfl; simp at ha]
--   | coe b' =>
--   lift b to ℕ using (hle.trans_lt (coe_lt_top _)).ne
--   simp [← pow_add, ← Nat.cast_add]

-- protected lemma ENat.mul_pow (a a' b : ℕ∞) : (a * a') ^ b = a ^ b * a' ^ b := by
--   cases b using ENat.recTopCoe with
--   | top =>
--     simp_rw [ENat.pow_top_eq_ite]
--     split_ifs <;> simp_all [ENat.mul_eq_one]
--   | coe b =>
--   simp [mul_pow]

end ENatLemmas

namespace ENat

noncomputable def card (α : Type*) : ℕ∞ := sSup ((↑) '' {n : ℕ | Nonempty (Fin n ↪ α)})

lemma nonempty_fintype_or_infinite (α : Type*) : Nonempty (Fintype α) ∨ Infinite α :=
  (finite_or_infinite α).elim (fun _ ↦ .inl ⟨Fintype.ofFinite α⟩) .inr

lemma Infinite.nonempty_fin_embedding (α : Type*) [h : Infinite α] (n : ℕ) :
    Nonempty (Fin n ↪ α) := by
  obtain ⟨s, rfl⟩ := h.exists_subset_card_eq _ n
  exact ⟨s.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype fun x ↦ x ∈ s)⟩

@[simp]
theorem card_eq_coe_fintypeCard (α : Type*) [Fintype α] : card α = Fintype.card α := by
  refine (sSup_le ?_).antisymm <| le_sSup ⟨_, ⟨(Fintype.equivFin α).symm.toEmbedding⟩, rfl⟩
  rintro e ⟨n, ⟨φ⟩, rfl⟩
  simpa using Fintype.card_le_of_embedding <| φ.trans <| (Fintype.equivFin α).toEmbedding

@[simp high]
theorem card_eq_top_of_infinite (α : Type*) [Infinite α] : card α = ⊤ := by
  suffices ∀ (n : ℕ), ∃ a, Nonempty (Fin a ↪ α) ∧ n ≤ a by simpa [card, sSup_eq_top_iff]
  exact fun n ↦ ⟨n, Infinite.nonempty_fin_embedding α n, rfl.le⟩

theorem _root_.Infinite.eNat_card_eq (hα : Infinite α) : card α = ⊤ :=
  card_eq_top_of_infinite α

@[simp] lemma card_eq_top : card α = ⊤ ↔ Infinite α := by
  refine ⟨fun h ↦ not_finite_iff_infinite.1 fun hfin ↦ ?_, fun h ↦ card_eq_top_of_infinite α⟩
  simp [@card_eq_coe_fintypeCard α (Fintype.ofFinite α)] at h

@[simp] lemma card_ne_top : card α ≠ ⊤ ↔ Finite α := by
  rw [not_iff_comm, card_eq_top, not_finite_iff_infinite]

@[simp] theorem card_lt_top_of_finite [Finite α] : card α < ⊤ := by
  simpa [lt_top_iff_ne_top, Ne]

@[simp] theorem card_ne_top_of_finite [Finite α] : card α ≠ ⊤ := by
  simpa

protected theorem card_le_card_of_injective {f : α → β} (hf : Function.Injective f) :
    card α ≤ card β := by
  obtain ⟨⟨hfin⟩⟩ | hinf := nonempty_fintype_or_infinite β
  · have hα := @Fintype.ofFinite _ <| Finite.of_injective f hf
    rw [card_eq_coe_fintypeCard, card_eq_coe_fintypeCard, Nat.cast_le]
    exact Fintype.card_le_of_injective f hf
  simp

alias _root_.Function.Injective.eNatCard_le := ENat.card_le_card_of_injective

theorem _root_.Function.Embedding.eNatCard_le (f : α ↪ β) : card α ≤ card β :=
  f.injective.eNatCard_le

protected theorem card_le_card_of_surjective {f : α → β} (hf : Surjective f) :
    ENat.card β ≤ ENat.card α := by
  obtain ⟨⟨h⟩⟩ | h := nonempty_fintype_or_infinite α
  · have := @Fintype.ofFinite _ <| Finite.of_surjective _ hf
    simp only [card_eq_coe_fintypeCard, Nat.cast_le, ge_iff_le]
    exact Fintype.card_le_of_surjective f hf
  simp [h.eNat_card_eq]

alias _root_.Function.Surjective.eNatCard_le := ENat.card_le_card_of_surjective

lemma card_eq_card_of_bijective {f : α → β} (hf : Bijective f) : ENat.card α = ENat.card β :=
  hf.injective.eNatCard_le.antisymm hf.surjective.eNatCard_le

alias _root_.Function.Bijective.eNatCard_eq := card_eq_card_of_bijective

theorem card_congr (f : α ≃ β) : card α = card β :=
  f.bijective.eNatCard_eq

protected theorem bijective_iff_surjective_and_card [Finite α] (f : α → β) :
    Bijective f ↔ Surjective f ∧ card α = card β := by
  have hα := Fintype.ofFinite α
  obtain ⟨⟨hβ⟩⟩ | hβ := nonempty_fintype_or_infinite β
  · simp_rw [card_eq_coe_fintypeCard, Nat.cast_inj, Fintype.bijective_iff_surjective_and_card]
  simp [Bijective, not_surjective_finite_infinite]

protected theorem bijective_iff_injective_and_card [Finite β] (f : α → β) :
    Bijective f ↔ Injective f ∧ card α = card β := by
  have hβ := Fintype.ofFinite β
  obtain ⟨⟨hα⟩⟩ | hα := nonempty_fintype_or_infinite α
  · simp_rw [card_eq_coe_fintypeCard, Nat.cast_inj, Fintype.bijective_iff_injective_and_card]
  simp [Bijective, not_injective_infinite_finite]

theorem _root_.Function.Injective.bijective_of_eNatCard_le [Finite β] {f : α → β}
    (inj : Injective f) (hc : card β ≤ card α) : Bijective f :=
  (ENat.bijective_iff_injective_and_card _).2 ⟨inj, inj.eNatCard_le.antisymm hc⟩

theorem _root_.Function.Surjective.bijective_of_eNatCard_le [Finite α] {f : α → β}
    (surj : Surjective f) (hc : card α ≤ card β) : Bijective f :=
  (ENat.bijective_iff_surjective_and_card _).2 ⟨surj, hc.antisymm surj.eNatCard_le⟩

theorem card_eq_zero_iff_isEmpty (α : Type*) : card α = 0 ↔ IsEmpty α := by
  obtain ⟨⟨hfin⟩⟩ | hinf := nonempty_fintype_or_infinite α
  · rw [card_eq_coe_fintypeCard, Nat.cast_eq_zero, Fintype.card_eq_zero_iff]
  simp [hinf.eNat_card_eq]

@[simp]
theorem card_eq_zero (α : Type*) [IsEmpty α] : card α = 0 := by
  rwa [card_eq_zero_iff_isEmpty]

@[simp]
theorem one_le_card_iff_nonempty (α : Type*) : 1 ≤ card α ↔ Nonempty α := by
  simp [one_le_iff_ne_zero, Ne, card_eq_zero_iff_isEmpty]

@[simp]
theorem card_sum (α β : Type*) : card (α ⊕ β) = card α + card β := by
  obtain ⟨⟨hfin⟩⟩ | hinf := nonempty_fintype_or_infinite (α ⊕ β)
  · have hα := @Fintype.ofFinite α (Finite.sum_left β)
    have hβ := @Fintype.ofFinite β (Finite.sum_right α)
    simp only [card_eq_coe_fintypeCard, ← Nat.cast_add, Nat.cast_inj]
    convert @Fintype.card_sum α β hα hβ
  obtain h | h := infinite_sum.1 hinf <;>
  simp [card_eq_top_of_infinite]

@[simp]
theorem card_prod (α β : Type*) : ENat.card (α × β) = ENat.card α * ENat.card β := by
  refine (isEmpty_or_nonempty α).elim (fun _ ↦ by simp) (fun hαne ↦ ?_)
  refine (isEmpty_or_nonempty β).elim (fun _ ↦ by simp) (fun hβne ↦ ?_)
  obtain ⟨⟨hα⟩⟩ | hβ := nonempty_fintype_or_infinite α <;>
  obtain ⟨⟨hβ⟩⟩ | hβ := nonempty_fintype_or_infinite β <;>
  simp

@[simp] lemma card_ulift (α : Type*) : card (ULift α) = card α := card_congr Equiv.ulift

@[simp] lemma card_plift (α : Type*) : card (PLift α) = card α := card_congr Equiv.plift

theorem card_image_of_injOn {α β : Type*} {f : α → β} {s : Set α} (h : Set.InjOn f s) :
    card (f '' s) = card s :=
  card_congr (Equiv.Set.imageOfInjOn f s h).symm

theorem card_image_of_injective {α β : Type*} (f : α → β) (s : Set α)
    (h : Function.Injective f) : card (f '' s) = card s := card_image_of_injOn h.injOn

theorem card_le_one_iff_subsingleton (α : Type*) : card α ≤ 1 ↔ Subsingleton α := by
  obtain ⟨⟨hfin⟩⟩ | hinf := nonempty_fintype_or_infinite α
  · rw [card_eq_coe_fintypeCard, Nat.cast_le_one, Fintype.card_le_one_iff_subsingleton]
  exact iff_of_false (by simp [hinf.eNat_card_eq]) (not_subsingleton α)

theorem one_lt_card_iff_nontrivial (α : Type*) : 1 < card α ↔ Nontrivial α := by
  rw [← not_le, card_le_one_iff_subsingleton, not_subsingleton_iff_nontrivial]

theorem card_eq_one_iff : card α = 1 ↔ Subsingleton α ∧ Nonempty α := by
  rw [le_antisymm_iff, card_le_one_iff_subsingleton, and_congr_right_iff, ← not_isEmpty_iff,
    ← card_eq_zero_iff_isEmpty, one_le_iff_ne_zero, Ne]
  exact fun _ ↦ Iff.rfl

theorem card_of_subsingleton (a : α) [Subsingleton α] : card α = 1 := by
  rwa [card_eq_one_iff, and_iff_left ⟨a⟩]

@[simp]
theorem card_unique [Nonempty α] [Subsingleton α] : card α = 1 := by
  simp [card_eq_one_iff, *]

theorem card_eq_two_iff : card α = 2 ↔ ∃ x y : α, x ≠ y ∧ {x, y} = @Set.univ α := by
  classical
  obtain hα | ⟨⟨hα⟩⟩ := (nonempty_fintype_or_infinite α).symm
  · simp only [card_eq_top_of_infinite, top_ne_ofNat, ne_eq, false_iff, not_exists, not_and]
    exact fun x y _ h ↦ by simpa [← h] using Set.infinite_univ (α := α)
  rw [card_eq_coe_fintypeCard, ← Finset.card_univ, show (2 : ℕ∞) = (2 : ℕ) from rfl,
    Nat.cast_inj, Finset.card_eq_two]
  simp [Set.ext_iff, Finset.ext_iff]

theorem card_eq_two_iff' (x : α) : card α = 2 ↔ ∃! y, y ≠ x := by
  rw [card_eq_two_iff]
  refine ⟨fun ⟨a, b, hab, heq⟩ ↦ ?_, fun ⟨y, hy, hy'⟩ ↦ ?_⟩
  · obtain rfl | rfl := heq.symm.subset (Set.mem_univ x)
    · exact ⟨b, hab.symm, fun y hya ↦ by simpa [hya] using heq.symm.subset <| Set.mem_univ y⟩
    exact ⟨a, hab, fun y hya ↦ by simpa [hya] using heq.symm.subset <| Set.mem_univ y⟩
  refine ⟨x, y, hy.symm, (Set.subset_univ _).antisymm fun a _ ↦ ?_⟩
  rw [Set.mem_insert_iff, or_iff_not_imp_left]
  exact hy' _

@[simp]
theorem card_subtype_true : card {_a : α // True} = card α :=
  card_congr <| Equiv.subtypeUnivEquiv fun _ => trivial

theorem card_sigma {β : α → Type*} [Fintype α] : ENat.card (Sigma β) = ∑ a, ENat.card (β a) := by
  by_cases ha : ∀ a, Finite (β a)
  · have (a : α) : Fintype (β a) := Fintype.ofFinite (β a)
    simp [ENat.card_eq_coe_fintypeCard, Fintype.card_sigma]
  obtain ⟨a, ha : Infinite (β a)⟩ := by simpa [not_finite_iff_infinite] using ha
  have _ : Infinite (Sigma β) := Infinite.sigma_of_right (a := a)
  rw [card_eq_top_of_infinite, eq_comm, eq_top_iff]
  simpa using Finset.univ.single_le_sum (f := fun a : α ↦ card (β a)) (by simp) (a := a) (by simp)

theorem card_pi {β : α → Type*} [Fintype α] : ENat.card (Π a, β a) = ∏ a, ENat.card (β a) := by
  classical
  obtain ⟨a, ha⟩ | h := em <| ∃ a, IsEmpty (β a)
  · rw [(card_eq_zero_iff_isEmpty _).2 (Function.isEmpty fun x ↦ x a), eq_comm,
      Finset.prod_eq_zero_iff]
    exact ⟨a, by simp, by simp⟩
  simp only [not_exists, not_isEmpty_iff] at h
  by_cases ha : ∀ a, Finite (β a)
  · have (a : α) : Fintype (β a) := Fintype.ofFinite (β a)
    simp [ENat.card_eq_coe_fintypeCard]
  obtain ⟨a, ha : Infinite (β a)⟩ := by simpa [not_finite_iff_infinite] using ha
  have _ : Infinite (Π a, β a) := Pi.infinite_of_exists_right a
  rw [card_eq_top_of_infinite, eq_comm, eq_top_iff]
  simpa using Finset.single_le_prod' (by simpa) (show a ∈ Finset.univ by simp)
    (f := fun x ↦ card (β x))

-- theorem card_fun : card (α → β) = card β ^ card α := by
--   classical
--   obtain hα | hα := isEmpty_or_nonempty α
--   · simp
--   obtain ⟨⟨hα⟩⟩ | hα := nonempty_fintype_or_infinite α
--   · obtain ⟨⟨hβ⟩⟩ | hβ := nonempty_fintype_or_infinite β
--     · simp [card_eq_coe_fintypeCard, Fintype.card_fun, Nat.cast_pow]
--     simp [top_pow Fintype.card_pos]
--   obtain hβ | hβ := isEmpty_or_nonempty β
--   · simp
--   obtain hβ' | hβ' := subsingleton_or_nontrivial β
--   · simp
--   simp only [card_eq_top_of_infinite]
--   rw [ENat.pow_top ((one_lt_card_iff_nontrivial _).2 hβ')]

theorem card_fun' [Fintype α] : card (α → β) = card β ^ Fintype.card α := by
  classical
  obtain hα | hα := isEmpty_or_nonempty α
  · simp
  obtain ⟨⟨hβ⟩⟩ | hβ := nonempty_fintype_or_infinite β
  · rw [card_eq_coe_fintypeCard, Fintype.card_fun, card_eq_coe_fintypeCard, Nat.cast_pow]
  rw [card_eq_top_of_infinite, card_eq_top_of_infinite, top_pow Fintype.card_pos]

end ENat


namespace Nat

/-- `Nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `Nat.card α = 0`. -/
protected def card (α : Type*) : ℕ := (ENat.card α).toNat

theorem card_eq_eNatCard_toNat (α : Type*) : Nat.card α = (ENat.card α).toNat := rfl

@[simp]
protected theorem cast_card (α : Type*) [Finite α] : (Nat.card α : ℕ∞) = ENat.card α := by
  rw [Nat.card, ENat.coe_toNat_eq_self]
  simpa

@[simp]
theorem card_eq_fintype_card [Fintype α] : Nat.card α = Fintype.card α := by
  rw [card_eq_eNatCard_toNat, ENat.card_eq_coe_fintypeCard, ENat.toNat_coe]

/-- Because this theorem takes `Fintype α` as a non-instance argument, it can be used in particular
when `Fintype.card` ends up with different instance than the one found by inference -/
theorem _root_.Fintype.card_eq_nat_card {_ : Fintype α} : Fintype.card α = Nat.card α := by
  rw [← card_eq_fintype_card]

lemma card_eq_finsetCard (s : Finset α) : Nat.card s = s.card := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe]

lemma card_eq_card_toFinset (s : Set α) [Fintype s] : Nat.card s = s.toFinset.card := by
  simp only [← Nat.card_eq_finsetCard, s.mem_toFinset]

lemma card_eq_card_finite_toFinset {s : Set α} (hs : s.Finite) : Nat.card s = hs.toFinset.card := by
  simp only [← Nat.card_eq_finsetCard, hs.mem_toFinset]

@[simp] theorem card_of_isEmpty [IsEmpty α] : Nat.card α = 0 := by
  simp [Nat.card]

@[simp] lemma card_eq_zero_of_infinite [Infinite α] : Nat.card α = 0 := by
  simp [Nat.card]

-- lemma cast_card [Finite α] : (Nat.card α : Cardinal) = Cardinal.mk α := by
--   rw [Nat.card, Cardinal.cast_toNat_of_lt_aleph0]
--   exact Cardinal.lt_aleph0_of_finite _

lemma _root_.Set.Infinite.card_eq_zero {s : Set α} (hs : s.Infinite) : Nat.card s = 0 :=
  @card_eq_zero_of_infinite _ hs.to_subtype

lemma card_eq_zero : Nat.card α = 0 ↔ IsEmpty α ∨ Infinite α := by
  simp [Nat.card, ENat.card_eq_zero_iff_isEmpty]

lemma card_ne_zero : Nat.card α ≠ 0 ↔ Nonempty α ∧ Finite α := by simp [card_eq_zero, not_or]

lemma card_pos_iff : 0 < Nat.card α ↔ Nonempty α ∧ Finite α := by
  rw [← card_ne_zero, Nat.pos_iff_ne_zero]

@[simp] lemma card_pos [Nonempty α] [Finite α] : 0 < Nat.card α := card_pos_iff.2 ⟨‹_›, ‹_›⟩

theorem finite_of_card_ne_zero (h : Nat.card α ≠ 0) : Finite α := (card_ne_zero.1 h).2

theorem card_congr (f : α ≃ β) : Nat.card α = Nat.card β :=
  congr_arg _ <| ENat.card_congr f

lemma card_le_card_of_injective [Finite β] {f : α → β} (hf : Injective f) :
    Nat.card α ≤ Nat.card β :=
  ENat.toNat_le_toNat hf.eNatCard_le ENat.card_ne_top_of_finite

alias _root_.Function.Injective.natCard_le := card_le_card_of_injective

lemma card_le_card_of_surjective [Finite α] {f : α → β} (hf : Surjective f) :
    Nat.card β ≤ Nat.card α :=
  ENat.toNat_le_toNat hf.eNatCard_le ENat.card_ne_top_of_finite

alias _root_.Function.Surjective.natCard_le := card_le_card_of_surjective

theorem card_eq_of_bijective {f : α → β} (hf : Function.Bijective f) : Nat.card α = Nat.card β :=
  card_congr (Equiv.ofBijective f hf)

alias _root_.Function.Bijective.natCard_eq := card_eq_of_bijective

protected theorem bijective_iff_injective_and_card [Finite β] (f : α → β) :
    Bijective f ↔ Injective f ∧ Nat.card α = Nat.card β := by
  rw [Bijective, and_congr_right_iff]
  intro h
  have := Fintype.ofFinite β
  have := Fintype.ofInjective f h
  revert h
  rw [← and_congr_right_iff, ← Bijective,
    card_eq_fintype_card, card_eq_fintype_card, Fintype.bijective_iff_injective_and_card]

protected theorem bijective_iff_surjective_and_card [Finite α] (f : α → β) :
    Bijective f ↔ Surjective f ∧ Nat.card α = Nat.card β := by
  classical
  rw [_root_.and_comm, Bijective, and_congr_left_iff]
  intro h
  have := Fintype.ofFinite α
  have := Fintype.ofSurjective f h
  revert h
  rw [← and_congr_left_iff, ← Bijective, ← and_comm,
    card_eq_fintype_card, card_eq_fintype_card, Fintype.bijective_iff_surjective_and_card]

theorem _root_.Function.Injective.bijective_of_nat_card_le [Finite β] {f : α → β}
    (inj : Injective f) (hc : Nat.card β ≤ Nat.card α) : Bijective f :=
  (Nat.bijective_iff_injective_and_card f).2 ⟨inj, hc.antisymm inj.natCard_le |>.symm⟩

theorem _root_.Function.Surjective.bijective_of_nat_card_le [Finite α] {f : α → β}
    (surj : Surjective f) (hc : Nat.card α ≤ Nat.card β) : Bijective f :=
  (Nat.bijective_iff_surjective_and_card f).2 ⟨surj, hc.antisymm surj.natCard_le⟩

theorem card_eq_of_equiv_fin {α : Type*} {n : ℕ} (f : α ≃ Fin n) : Nat.card α = n := by
  simpa only [card_eq_fintype_card, Fintype.card_fin] using card_congr f

section Set
open Set
variable {s t : Set α}

-- lemma card_mono (ht : t.Finite) (h : s ⊆ t) : Nat.card s ≤ Nat.card t :=
--   toNat_le_toNat (mk_le_mk_of_subset h) ht.lt_aleph0

-- lemma card_image_le {f : α → β} (hs : s.Finite) : Nat.card (f '' s) ≤ Nat.card s :=
--   have := hs.to_subtype; card_le_card_of_surjective (imageFactorization f s)
-- surjective_onto_image

-- lemma card_image_of_injOn {f : α → β} (hf : s.InjOn f) : Nat.card (f '' s) = Nat.card s := by
--   classical
--   obtain hs | hs := s.finite_or_infinite
--   · have := hs.fintype
--     have := fintypeImage s f
--     simp_rw [Nat.card_eq_fintype_card, Set.card_image_of_inj_on hf]
--   · have := hs.to_subtype
--     have := (hs.image hf).to_subtype
--     simp [Nat.card_eq_zero_of_infinite]

-- lemma card_image_of_injective {f : α → β} (hf : Injective f) (s : Set α) :
--     Nat.card (f '' s) = Nat.card s := card_image_of_injOn hf.injOn

-- lemma card_image_equiv (e : α ≃ β) : Nat.card (e '' s) = Nat.card s :=
--     Nat.card_congr (e.image s).symm

-- lemma card_preimage_of_injOn {f : α → β} {s : Set β} (hf : (f ⁻¹' s).InjOn f)
-- (hsf : s ⊆ range f) :
--     Nat.card (f ⁻¹' s) = Nat.card s := by
--   rw [← Nat.card_image_of_injOn hf, image_preimage_eq_iff.2 hsf]

-- lemma card_preimage_of_injective {f : α → β} {s : Set β} (hf : Injective f) (hsf : s ⊆ range f) :
--     Nat.card (f ⁻¹' s) = Nat.card s := card_preimage_of_injOn hf.injOn hsf

-- @[simp] lemma card_univ : Nat.card (univ : Set α) = Nat.card α :=
--   card_congr (Equiv.Set.univ α)

-- lemma card_range_of_injective {f : α → β} (hf : Injective f) :
--     Nat.card (range f) = Nat.card α := by
--   rw [← Nat.card_preimage_of_injective hf le_rfl]
--   simp

end Set

/-- If the cardinality is positive, that means it is a finite type, so there is
an equivalence between `α` and `Fin (Nat.card α)`. See also `Finite.equivFin`. -/
def equivFinOfCardPos {α : Type*} (h : Nat.card α ≠ 0) : α ≃ Fin (Nat.card α) := by
  cases fintypeOrInfinite α
  · simpa only [card_eq_fintype_card] using Fintype.equivFin α
  · simp only [card_eq_zero_of_infinite, ne_eq, not_true_eq_false] at h

theorem card_of_subsingleton (a : α) [Subsingleton α] : Nat.card α = 1 := by
  rw [← Nat.cast_inj (R := ℕ∞), Nat.cast_card]
  exact ENat.card_of_subsingleton a

theorem card_eq_one_iff_unique : Nat.card α = 1 ↔ Subsingleton α ∧ Nonempty α := by
  simp [Nat.card, ENat.toNat_eq_iff, ENat.card_eq_one_iff]


@[simp]
theorem card_unique [Nonempty α] [Subsingleton α] : Nat.card α = 1 := by
  simp [card_eq_one_iff_unique, *]

theorem card_eq_one_iff_exists : Nat.card α = 1 ↔ ∃ x : α, ∀ y : α, y = x := by
  rw [card_eq_one_iff_unique]
  exact ⟨fun ⟨s, ⟨a⟩⟩ ↦ ⟨a, fun x ↦ s.elim x a⟩, fun ⟨x, h⟩ ↦ ⟨subsingleton_of_forall_eq x h, ⟨x⟩⟩⟩

theorem card_eq_two_iff : Nat.card α = 2 ↔ ∃ x y : α, x ≠ y ∧ {x, y} = @Set.univ α := by
  rw [Nat.card, ENat.toNat_eq_iff (by simp), Nat.cast_two, ENat.card_eq_two_iff]

theorem card_eq_two_iff' (x : α) : Nat.card α = 2 ↔ ∃! y, y ≠ x := by
  rw [Nat.card, ENat.toNat_eq_iff (by simp), Nat.cast_two, ENat.card_eq_two_iff']

@[simp]
theorem card_subtype_true : Nat.card {_a : α // True} = Nat.card α :=
  card_congr <| Equiv.subtypeUnivEquiv fun _ => trivial

@[simp]
theorem card_sum [Finite α] [Finite β] : Nat.card (α ⊕ β) = Nat.card α + Nat.card β := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_sum]

@[simp]
theorem card_prod (α β : Type*) : Nat.card (α × β) = Nat.card α * Nat.card β := by
  simp [Nat.card, ENat.card_prod, ENat.toNat_mul]

@[simp]
theorem card_ulift (α : Type*) : Nat.card (ULift α) = Nat.card α :=
  card_congr Equiv.ulift

@[simp]
theorem card_plift (α : Type*) : Nat.card (PLift α) = Nat.card α :=
  card_congr Equiv.plift

theorem card_sigma {β : α → Type*} [Fintype α] [∀ a, Finite (β a)] :
    Nat.card (Sigma β) = ∑ a, Nat.card (β a) := by
  letI _ (a : α) : Fintype (β a) := Fintype.ofFinite (β a)
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_sigma]

theorem card_pi {β : α → Type*} [Fintype α] : Nat.card (∀ a, β a) = ∏ a, Nat.card (β a) := by
  simp [Nat.card, ENat.card_pi]

theorem card_fun [Finite α] : Nat.card (α → β) = Nat.card β ^ Nat.card α := by
  haveI := Fintype.ofFinite α
  rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card]

@[simp]
theorem card_zmod (n : ℕ) : Nat.card (ZMod n) = n := by
  cases n
  · exact @Nat.card_eq_zero_of_infinite _ Int.infinite
  · rw [Nat.card_eq_fintype_card, ZMod.card]

end Nat

-- namespace Set
-- variable {s : Set α}

-- lemma card_singleton_prod (a : α) (t : Set β) : Nat.card ({a} ×ˢ t) = Nat.card t := by
--   rw [singleton_prod, Nat.card_image_of_injective (Prod.mk.inj_left a)]

-- lemma card_prod_singleton (s : Set α) (b : β) : Nat.card (s ×ˢ {b}) = Nat.card s := by
--   rw [prod_singleton, Nat.card_image_of_injective (Prod.mk.inj_right b)]

-- theorem natCard_pos (hs : s.Finite) : 0 < Nat.card s ↔ s.Nonempty := by
--   simp [pos_iff_ne_zero, Nat.card_eq_zero, hs.to_subtype, nonempty_iff_ne_empty]

-- protected alias ⟨_, Nonempty.natCard_pos⟩ := natCard_pos

-- @[simp] lemma natCard_graphOn (s : Set α) (f : α → β) : Nat.card (s.graphOn f) = Nat.card s := by
--   rw [← Nat.card_image_of_injOn fst_injOn_graph, image_fst_graphOn]

-- end Set


-- namespace ENat

-- /-- `ENat.card α` is the cardinality of `α` as an extended natural number.
--   If `α` is infinite, `ENat.card α = ⊤`. -/
-- def card (α : Type*) : ℕ∞ :=
--   toENat (mk α)

-- @[simp]
-- theorem card_eq_coe_fintype_card [Fintype α] : card α = Fintype.card α := by
--   simp [card]

-- @[simp high]
-- theorem card_eq_top_of_infinite [Infinite α] : card α = ⊤ := by
--   simp only [card, toENat_eq_top, aleph0_le_mk]

-- @[simp] lemma card_eq_top : card α = ⊤ ↔ Infinite α := by simp [card, aleph0_le_mk_iff]

-- @[simp] theorem card_lt_top_of_finite [Finite α] : card α < ⊤ := by simp [card]

-- @[simp]
-- theorem card_sum (α β : Type*) :
--     card (α ⊕ β) = card α + card β := by
--   simp only [card, mk_sum, map_add, toENat_lift]

-- theorem card_congr {α β : Type*} (f : α ≃ β) : card α = card β :=
--   Cardinal.toENat_congr f

-- @[simp] lemma card_ulift (α : Type*) : card (ULift α) = card α := card_congr Equiv.ulift

-- @[simp] lemma card_plift (α : Type*) : card (PLift α) = card α := card_congr Equiv.plift

-- theorem card_image_of_injOn {α β : Type*} {f : α → β} {s : Set α} (h : Set.InjOn f s) :
--     card (f '' s) = card s :=
--   card_congr (Equiv.Set.imageOfInjOn f s h).symm

-- theorem card_image_of_injective {α β : Type*} (f : α → β) (s : Set α)
--     (h : Function.Injective f) : card (f '' s) = card s := card_image_of_injOn h.injOn

-- @[simp]
-- theorem _root_.Cardinal.natCast_le_toENat_iff {n : ℕ} {c : Cardinal} :
--     ↑n ≤ toENat c ↔ ↑n ≤ c := by
--   rw [← toENat_nat n, toENat_le_iff_of_le_aleph0 (le_of_lt (nat_lt_aleph0 n))]

-- theorem _root_.Cardinal.toENat_le_natCast_iff {c : Cardinal} {n : ℕ} :
--     toENat c ≤ n ↔ c ≤ n := by simp

-- @[simp]
-- theorem _root_.Cardinal.natCast_eq_toENat_iff {n : ℕ} {c : Cardinal} :
--     ↑n = toENat c ↔ ↑n = c := by
--   rw [le_antisymm_iff, le_antisymm_iff, Cardinal.toENat_le_natCast_iff,
--     Cardinal.natCast_le_toENat_iff]

-- theorem _root_.Cardinal.toENat_eq_natCast_iff {c : Cardinal} {n : ℕ} :
--     Cardinal.toENat c = n ↔ c = n := by simp

-- @[simp]
-- theorem _root_.Cardinal.natCast_lt_toENat_iff {n : ℕ} {c : Cardinal} :
--     ↑n < toENat c ↔ ↑n < c := by
--   simp only [← not_le, Cardinal.toENat_le_natCast_iff]

-- @[simp]
-- theorem _root_.Cardinal.toENat_lt_natCast_iff {n : ℕ} {c : Cardinal} :
--     toENat c < ↑n ↔ c < ↑n := by
--   simp only [← not_le, Cardinal.natCast_le_toENat_iff]

-- theorem card_eq_zero_iff_empty (α : Type*) : card α = 0 ↔ IsEmpty α := by
--   rw [← Cardinal.mk_eq_zero_iff]
--   simp [card]

-- theorem card_le_one_iff_subsingleton (α : Type*) : card α ≤ 1 ↔ Subsingleton α := by
--   rw [← le_one_iff_subsingleton]
--   simp [card]

-- theorem one_lt_card_iff_nontrivial (α : Type*) : 1 < card α ↔ Nontrivial α := by
--   rw [← Cardinal.one_lt_iff_nontrivial]
--   conv_rhs => rw [← Nat.cast_one]
--   rw [← natCast_lt_toENat_iff]
--   simp only [ENat.card, Nat.cast_one]

-- end ENat
