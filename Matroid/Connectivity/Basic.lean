import Matroid.Minor.Rank
import Matroid.Modular.Basic
import Matroid.ForMathlib.Data.Set.Finite

open Set

variable {α : Type*} {M : Matroid α}

namespace Matroid

section Connected

variable {C K : Set α} {e f g : α}

def ConnectedTo (M : Matroid α) (e f : α) := (e = f ∧ e ∈ M.E) ∨ ∃ C, M.IsCircuit C ∧ e ∈ C ∧ f ∈ C

lemma ConnectedTo.exists_isCircuit_of_ne (h : M.ConnectedTo e f) (hne : e ≠ f) :
    ∃ C, M.IsCircuit C ∧ e ∈ C ∧ f ∈ C := by
  simpa [ConnectedTo, hne] using h

lemma IsCircuit.mem_connectedTo_mem (hC : M.IsCircuit C) (heC : e ∈ C) (hfC : f ∈ C) :
    M.ConnectedTo e f :=
  .inr ⟨C, hC, heC, hfC⟩

lemma connectedTo_self (he : e ∈ M.E) : M.ConnectedTo e e :=
  .inl ⟨rfl, he⟩

lemma ConnectedTo.symm (h : M.ConnectedTo e f) : M.ConnectedTo f e := by
  obtain (⟨rfl, hef⟩ | ⟨C, hC, heC, hfC⟩) := h
  · exact connectedTo_self hef
  exact .inr ⟨C, hC, hfC, heC⟩

lemma connectedTo_comm : M.ConnectedTo e f ↔ M.ConnectedTo f e :=
  ⟨ConnectedTo.symm, ConnectedTo.symm⟩

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma ConnectedTo.mem_ground_left (h : M.ConnectedTo e f) : e ∈ M.E := by
  obtain (⟨rfl, hef⟩ | ⟨C, hC, heC, -⟩) := h
  · exact hef
  exact hC.subset_ground heC

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma ConnectedTo.mem_ground_right (h : M.ConnectedTo e f) : f ∈ M.E :=
  h.symm.mem_ground_left

@[simp] lemma connectedTo_self_iff : M.ConnectedTo e e ↔ e ∈ M.E :=
  ⟨fun h ↦ h.mem_ground_left, connectedTo_self⟩

lemma ConnectedTo.isNonloop_left_of_ne (h : M.ConnectedTo e f) (hef : e ≠ f) : M.IsNonloop e := by
  obtain ⟨C, hC, heC, hfC⟩ := h.exists_isCircuit_of_ne hef
  exact hC.isNonloop_of_mem ⟨e, heC, f, hfC, hef⟩ heC

lemma ConnectedTo.isNonloop_right_of_ne (h : M.ConnectedTo e f) (hef : e ≠ f) : M.IsNonloop f :=
  h.symm.isNonloop_left_of_ne hef.symm

lemma ConnectedTo.to_dual (h : M.ConnectedTo e f) : M✶.ConnectedTo e f := by
  obtain rfl | hne := eq_or_ne e f; exact connectedTo_self h.mem_ground_left
  obtain ⟨C, hC, heC, hfC⟩ := h.exists_isCircuit_of_ne hne
  have hpara : (M ／ (C \ {e,f})).Parallel e f := by
    rw [parallel_iff_isCircuit hne]
    apply hC.contract_diff_isCircuit (by simp) (by simp [pair_subset_iff, heC, hfC])
  obtain ⟨B, hB, heB⟩ := hpara.isNonloop_left.exists_mem_isBase
  have hK := fundCocircuit_cocircuit heB hB
  refine IsCircuit.mem_connectedTo_mem hK.of_contract.isCircuit (mem_fundCocircuit _ _ _) ?_
  exact hpara.mem_cocircuit_of_mem hK (mem_fundCocircuit _ _ _)

lemma ConnectedTo.of_dual (h : M✶.ConnectedTo e f) : M.ConnectedTo e f := by
  simpa using h.to_dual

@[simp] lemma connectedTo_dual_iff : M✶.ConnectedTo e f ↔ M.ConnectedTo e f :=
  ⟨ConnectedTo.of_dual, ConnectedTo.to_dual⟩

lemma Cocircuit.mem_connectedTo_mem (hK : M.Cocircuit K) (heK : e ∈ K) (hfK : f ∈ K) :
    M.ConnectedTo e f :=
  (hK.isCircuit.mem_connectedTo_mem heK hfK).of_dual

lemma ConnectedTo.exists_cocircuit_of_ne (h : M.ConnectedTo e f) (hne : e ≠ f) :
    ∃ K, M.Cocircuit K ∧ e ∈ K ∧ f ∈ K :=
  h.to_dual.exists_isCircuit_of_ne hne

lemma ConnectedTo.of_restrict {R : Set α} (hR : R ⊆ M.E) (hef : (M ↾ R).ConnectedTo e f) :
    M.ConnectedTo e f := by
  obtain (rfl | hne) := eq_or_ne e f
  · simp [hR hef.mem_ground_left]
  obtain ⟨C, hC, heC, hfC⟩ := hef.exists_isCircuit_of_ne hne
  rw [restrict_isCircuit_iff] at hC
  exact hC.1.mem_connectedTo_mem heC hfC

lemma ConnectedTo.of_delete {D : Set α} (hef : (M ＼ D).ConnectedTo e f) : M.ConnectedTo e f := by
  rw [delete_eq_restrict] at hef; apply hef.of_restrict diff_subset

lemma ConnectedTo.of_contract {C : Set α} (hef : (M ／ C).ConnectedTo e f) : M.ConnectedTo e f := by
  replace hef := hef.to_dual
  rw [contract_dual_eq_dual_delete] at hef
  exact hef.of_delete.of_dual

lemma ConnectedTo.of_minor {N : Matroid α} (hef : N.ConnectedTo e f) (h : N ≤m M) :
    M.ConnectedTo e f := by
  obtain ⟨C, D, -, -, -, rfl⟩ := h; exact hef.of_delete.of_contract

private lemma connectedTo_of_indep_isHyperplane_of_not_coloop {I : Set α} (hI : M.Indep I)
    (hI' : M.IsHyperplane I) (heI : e ∈ M.E \ I) (hfI : f ∈ I) (hf : ¬ M.Coloop f) :
    M.ConnectedTo e f := by
  have hB : M.IsBase (insert e I) := by
    refine Indep.isBase_of_spanning ?_ (hI'.spanning_of_ssuperset (ssubset_insert heI.2))
    · rwa [hI.insert_indep_iff_of_not_mem heI.2, hI'.isFlat.closure]
  simp only [hB.mem_coisLoop_iff_forall_not_mem_fundCircuit (.inr hfI), mem_diff, mem_insert_iff,
    not_or, and_imp, not_forall, Classical.not_imp, not_not, exists_prop, exists_and_left] at hf
  obtain ⟨x, hx, hxe, hxI, hfC⟩ := hf
  have hxi : M.Indep ((insert x I) \ {e}) := by
    rw [diff_singleton_eq_self (by simp [Ne.symm hxe, heI.2]), hI.insert_indep_iff_of_not_mem hxI,
      hI'.isFlat.closure]
    exact ⟨hx, hxI⟩
  have hC := IsBase.fundCircuit_isCircuit hB hx (by simp [hxe, hxI])

  refine hC.mem_connectedTo_mem (by_contra fun heC ↦ ?_) hfC

  have hss := subset_diff_singleton (fundCircuit_subset_insert _ x (insert e I)) heC
  simp only [insert_comm, mem_singleton_iff, insert_diff_of_mem] at hss
  exact hC.dep.not_indep (hxi.subset hss)

lemma ConnectedTo.trans {e₁ e₂ : α} (h₁ : M.ConnectedTo e₁ f) (h₂ : M.ConnectedTo f e₂) :
    M.ConnectedTo e₁ e₂ := by
  obtain (rfl | hne) := eq_or_ne e₁ e₂; simp [h₁.mem_ground_left]
  obtain (rfl | hne₁) := eq_or_ne e₁ f; assumption
  obtain (rfl | hne₂) := eq_or_ne f e₂; assumption
  obtain ⟨C₁, hC₁, heC₁, hfC₁⟩ := h₁.exists_isCircuit_of_ne hne₁
  obtain ⟨C₂, hC₂, hfC₂, h⟩ := h₂.exists_isCircuit_of_ne hne₂
  obtain ⟨K₁, hK₁, he₁K₁, hfK₁⟩ := h₁.exists_cocircuit_of_ne hne₁
  obtain ⟨C₂, hC₂, hfC₂, he₂C₂⟩ := h₂.exists_isCircuit_of_ne hne₂

  by_cases he₂K₁ : e₂ ∈ K₁; exact (hK₁.mem_connectedTo_mem he₁K₁ he₂K₁)

  have hC₂i : M.Indep (C₂ \ K₁) := (hC₂.diff_singleton_indep hfC₂).subset
      (subset_diff_singleton diff_subset (by simp [hfK₁]))

  have hH := hK₁.compl_isHyperplane

  obtain ⟨J, hJ, he₂J⟩ :=
    hC₂i.subset_isBasis_of_subset (diff_subset_diff_left hC₂.subset_ground) hH.subset_ground

  refine (connectedTo_of_indep_isHyperplane_of_not_coloop ?_
    (hH.isBasis_isHyperplane_delete hJ) ?_ ?_ ?_).of_delete
  · simp [disjoint_sdiff_right, hJ.indep]
  · simpa [h₁.mem_ground_left, he₁K₁] using
      not_mem_subset hJ.subset (by simp [he₁K₁, h₁.mem_ground_left])
  · exact he₂J ⟨he₂C₂, he₂K₁⟩

  refine IsCircuit.not_coisLoop_of_mem ?_ he₂C₂
  rwa [delete_isCircuit_iff, and_iff_right hC₂, disjoint_iff_inter_eq_empty, ← inter_diff_assoc,
    diff_eq_empty, ← inter_diff_assoc, inter_eq_self_of_subset_left hC₂.subset_ground]

@[mk_iff]
structure Connected (M : Matroid α) : Prop where
  nonempty : M.Nonempty
  forall_connectedTo : ∀ ⦃e f⦄, e ∈ M.E → f ∈ M.E → M.ConnectedTo e f

lemma Connected.connectedTo (hM : M.Connected) (x y : α) (hx : x ∈ M.E := by aesop_mat)
    (hy : y ∈ M.E := by aesop_mat) : M.ConnectedTo x y :=
  hM.forall_connectedTo hx hy

lemma Connected.to_dual (hM : M.Connected) : M✶.Connected :=
  ⟨by have := hM.1; apply dual_nonempty, fun _ _ he hf ↦ (hM.2 he hf).to_dual⟩

lemma Connected.of_dual (hM : M✶.Connected) : M.Connected := by
  simpa using hM.to_dual

@[simp] lemma connected_dual_iff : M✶.Connected ↔ M.Connected :=
  ⟨Connected.of_dual, Connected.to_dual⟩

lemma Coloop.not_connected (he : M.Coloop e) (hE : M.E.Nontrivial) : ¬ M.Connected := by
  obtain ⟨f, hfE, hfe⟩ := hE.exists_ne e
  rintro ⟨-, hconn⟩
  obtain ⟨K, hK, heK, -⟩ := (hconn he.mem_ground hfE).exists_isCircuit_of_ne hfe.symm
  exact he.not_mem_isCircuit hK heK

lemma IsLoop.not_connected (he : M.IsLoop e) (hE : M.E.Nontrivial) : ¬ M.Connected := by
  rw [← connected_dual_iff]
  exact he.dual_coloop.not_connected hE

lemma Connected.loopless (hM : M.Connected) (hE : M.E.Nontrivial) : M.Loopless := by
  rw [loopless_iff_forall_not_isLoop]
  exact fun e _ hl ↦ hl.not_connected hE hM

lemma Connected.exists_isCircuit_of_ne (h : M.Connected) (he : e ∈ M.E) (hf : f ∈ M.E)
    (hne : e ≠ f) : ∃ C, M.IsCircuit C ∧ e ∈ C ∧ f ∈ C :=
  (h.2 he hf).exists_isCircuit_of_ne hne

lemma Connected.exists_isCircuit (h : M.Connected) (hM : M.E.Nontrivial) (he : e ∈ M.E)
    (hf : f ∈ M.E) : ∃ C, M.IsCircuit C ∧ e ∈ C ∧ f ∈ C := by
  obtain (rfl | hne) := eq_or_ne e f
  · obtain (he' | he') := em (M.Coloop e)
    · exact False.elim <| he'.not_connected hM h
    obtain ⟨C, hC, heC⟩ := exists_mem_isCircuit_of_not_coloop he he'
    exact ⟨C, hC, heC, heC⟩
  exact (h.2 he hf).exists_isCircuit_of_ne hne

lemma singleton_connected (hM : M.E = {e}) : M.Connected :=
  ⟨⟨by simp [hM]⟩, by simp [hM]⟩


section FinitaryCofinitary

variable [DecidablePred (Set.Infinite (α := Set α))]

private def cSet (Cs : ℕ → Set α) (e : ℕ → α) : ℕ → Set (Set α)
  | 0 => range Cs
  | n + 1 =>
      let C' := {C ∈ cSet Cs e n | e (n+1) ∈ C}
      if C'.Infinite then C' else cSet Cs e n \ C'

private def X (Cs : ℕ → Set α) (e : ℕ → α) : ℕ → Set α
  | 0   => {e 0}
  | n+1 => if {C ∈ cSet Cs e n | e (n+1) ∈ C}.Infinite then insert (e (n+1)) (X Cs e n)
      else X Cs e n

lemma cSet_antitone {Cs : ℕ → Set α} {e : ℕ → α} : Antitone (cSet Cs e) := by
  apply antitone_nat_of_succ_le fun n ↦ ?_
  simp only [cSet]
  split_ifs with h <;> simp

lemma cSet_subset_range (Cs : ℕ → Set α) (e : ℕ → α) (i : ℕ) : cSet Cs e i ⊆ range Cs :=
  subset_trans (cSet_antitone (zero_le i)) rfl.le

lemma X_monotone (Cs : ℕ → Set α) (e : ℕ → α) : Monotone (X Cs e) := by
  apply monotone_nat_of_le_succ fun n ↦ ?_
  simp only [X]
  split_ifs with h <;> simp

lemma cSet_infinite (Cs : ℕ ↪ Set α) (e) (i : ℕ) : (cSet Cs e i).Infinite := by
  induction' i with i IH
  · simpa only [cSet] using infinite_range_of_injective Cs.injective
  simp only [cSet] at IH ⊢
  split_ifs with h
  · simpa
  exact Infinite.diff IH (by exact not_infinite.1 h)

lemma cSet_inter_image_Iic {Cs : ℕ ↪ Set α} {e} {i : ℕ} {C} (heC : e 0 ∈ C) (hC : C ∈ cSet Cs e i) :
    C ∩ e '' Iic i = X Cs e i := by
  induction' i with i IH
  · simpa [X, Set.Iic]
  simp only [X, Finset.range_add_one (n := i+1)]
  specialize IH (cSet_antitone (by simp) hC)
  have aux : ∀ n, Iic n = Finset.range (n+1) := by simp [Set.ext_iff, Nat.lt_add_one_iff]
  rw [aux] at IH ⊢
  rw [← IH, insert_inter_distrib, ← image_insert_eq, ← Finset.coe_insert, ← Finset.range_add_one]
  split_ifs with h'
  · obtain ⟨-, heC⟩ : _ ∧ e (i+1) ∈ C := by simpa [cSet, h'] using hC
    rw [insert_inter_of_mem (mem_image_of_mem _ (by simp)),
      insert_eq_of_mem (mem_inter heC <| mem_image_of_mem _ (by simp))]
  simp only [cSet, h', ↓reduceIte, mem_diff, mem_setOf_eq, not_and] at hC
  rw [Finset.range_add_one, Finset.coe_insert, image_insert_eq, inter_comm,
    insert_inter_of_not_mem (hC.2 hC.1), inter_comm]

/-- Every connected, finitary, cofinitary matroid is finite -/
theorem Connected.finite_of_finitary_of_cofinitary {α : Type*} {M : Matroid α} (hM : M.Connected)
    [Finitary M] [Finitary M✶] : M.Finite := by
  classical
  refine ⟨by_contra fun hinf ↦ ?_⟩

  have hcinf : ∀ e ∈ M.E, {C | M.IsCircuit C ∧ e ∈ C}.Infinite := by
    intro e he hfin
    have hfin' := Set.Finite.sUnion hfin (fun C hC ↦ hC.1.finite)
    obtain ⟨f, hf⟩ := (Infinite.diff hinf hfin').nonempty
    obtain ⟨C, hC, heC, hfC⟩ := hM.exists_isCircuit (Infinite.nontrivial hinf) he hf.1
    exact hf.2 ⟨C, ⟨hC, heC⟩, hfC⟩

  -- Choose an element `e₀`, a sequence of distinct circuits containing `e₀`, and an enumeration `e`
  -- of the union of these circuits.
  obtain ⟨e, Cs, hCs, he⟩ : ∃ (e : ℕ ↪ α) (Cs : ℕ ↪ Set α),
      (∀ i, e 0 ∈ Cs i ∧ M.IsCircuit (Cs i)) ∧ range e = ⋃ i, Cs i := by
    obtain ⟨e₀, he₀⟩ := Set.Infinite.nonempty hinf
    set Cs' := (hcinf e₀ he₀).natEmbedding
    set U := (⋃ i, (Cs' i).1)
    have he₀U : e₀ ∈ U := mem_iUnion.2 ⟨0, (Cs' 0).2.2⟩

    have : Countable U := (countable_iUnion (fun i ↦ (Cs' i).2.1.finite.countable)).to_subtype
    have : Infinite U  := (infinite_iUnion (Subtype.val_injective.comp Cs'.injective)).to_subtype

    obtain ⟨f : ℕ ≃ U⟩ := nonempty_equiv_of_countable (α := ℕ) (β := U)
    set e := (Equiv.swap (f.symm ⟨e₀, he₀U⟩) 0).trans f

    refine ⟨e.toEmbedding.trans <| Function.Embedding.subtype _,
      Cs'.trans <| Function.Embedding.subtype _, fun i ↦ ?_, ?_⟩
    · suffices M.IsCircuit (Cs' i).1 ∧ e₀ ∈ (Cs' i).1 by simpa [e, and_comm]
      exact (Cs' i).2
    suffices U = ⋃ i, (Cs' i).1 by simpa [Function.Embedding.trans]
    rfl

  -- Restrict `M` to the union of the circuits.
  set M' := M ↾ range e with hM'
  have : M'✶.Finitary := by
    rw [hM', ← delete_compl, delete_dual_eq_dual_contract]
    exact contract_finitary

  set X := X Cs e with hX
  set cSet := cSet Cs e

  have h0 : ∀ {i C}, C ∈ cSet i → (e 0 ∈ C ∧ M'.IsCircuit C) := by
    refine @fun i C h ↦ ?_
    obtain ⟨j, rfl⟩ : ∃ (i : ℕ), Cs i = C := by simpa [cSet, Matroid.cSet] using
      (show C ∈ cSet 0 from cSet_antitone (zero_le _) h)
    exact ⟨(hCs j).1,
      (hCs j).2.isCircuit_restrict_of_subset <|(subset_iUnion ..).trans he.symm.subset⟩

  have hXE : ⋃ i, X i ⊆ M'.E := by
    refine iUnion_subset fun i ↦ ?_
    induction' i with i IH
    · simp [X, Matroid.X, M']
    simp only [hX, restrict_ground_eq, M', Matroid.X]
    split_ifs <;> simpa [insert_subset_iff]

  have hd : M'.Dep (⋃ i, X i) := by
    rw [← not_indep_iff hXE]
    refine fun hi ↦ ?_
    obtain ⟨K, hK, hKX⟩ := hi.exists_cocircuit_inter_eq_mem (e := e 0) (mem_iUnion_of_mem 0 <| rfl)
    obtain ⟨A, rfl⟩ := subset_range_iff_exists_image_eq.1 <| hK.subset_ground
    obtain ⟨m, hm : A ⊆ Iic m⟩ := (Finite.of_finite_image hK.finite e.injective.injOn).bddAbove
    obtain ⟨C, hC : C ∈ cSet m⟩ := (cSet_infinite Cs e m).nonempty

    have hi : C ∩ (e '' A) = {e 0} := by
      rw [inter_comm]
      simp_rw [← hKX, subset_antisymm_iff, subset_inter_iff, inter_subset_left, true_and, hKX,
        singleton_subset_iff, and_iff_left <| (h0 hC).1, inter_comm]
      refine (inter_subset_inter_right _ (image_subset _ hm)).trans ?_
      rw [cSet_inter_image_Iic (h0 hC).1 hC ]
      exact subset_iUnion _ m

    exact (h0 hC).2.inter_cocircuit_ne_singleton hK hi

  obtain ⟨C, hCX, hC⟩ := hd.exists_isCircuit_subset
  obtain ⟨B, hB, hCB⟩ := finite_subset_iUnion hC.finite hCX
  obtain ⟨m, hm : ∀ _, _⟩ := hB.bddAbove

  have hCm : C ⊆ X m := hCB.trans (iUnion₂_subset fun i hib ↦ (X_monotone _ _ <| hm i hib))
  obtain ⟨C', hC' : C' ∈ cSet _, hCC'⟩ := (cSet_infinite Cs e m).nontrivial.exists_ne C

  have hss := (hCm.trans (cSet_inter_image_Iic (h0 hC').1 hC').symm.subset).trans inter_subset_left
  exact False.elim <| hC.dep.not_indep <| (h0 hC').2.ssubset_indep (hss.ssubset_of_ne hCC'.symm)


end FinitaryCofinitary

end Connected
