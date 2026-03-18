import Matroid.Modular.Flat
import Matroid.Axioms.Flat

variable {α ι : Type*} {M N : Matroid α} {X Y C F F' F₀ F₁ T : Set α} {e f g : α}

set_option linter.style.longLine false

open Set

namespace Matroid

@[pp_nodot]
structure SumFlat (M N : Matroid α) (F : Set α) : Prop where
  isFlat_left : M.IsFlat (F ∩ M.E)
  isFlat_right : N.IsFlat (F ∩ N.E)
  subset_union : F ⊆ M.E ∪ N.E

structure SumFlat' (M N : Matroid α) (F₀ F₁ F : Set α) : Prop where
  isFlat_left : M.IsFlat F₀
  isFlat_right : N.IsFlat F₁
  inter_left : F ∩ M.E = F₀
  inter_right : F ∩ N.E = F₁
  union_eq : F₀ ∪ F₁ = F

lemma sumFlat'_of_subset_subset (hF₀ : M.IsFlat F₀) (hF₁ : N.IsFlat F₁) (h₀ : F₀ ∩ N.E ⊆ F₁)
    (h₁ : F₁ ∩ M.E ⊆ F₀) : SumFlat' M N F₀ F₁ (F₀ ∪ F₁) := by
  refine ⟨hF₀, hF₁, ?_, ?_, rfl⟩
  · rwa [union_inter_distrib_right, inter_eq_self_of_subset_left hF₀.subset_ground, union_eq_left]
  rwa [union_inter_distrib_right, inter_eq_self_of_subset_left hF₁.subset_ground, union_eq_right]

lemma sumFlat'_ground_ground (M N : Matroid α) : SumFlat' M N M.E N.E (M.E ∪ N.E) := by
  apply sumFlat'_of_subset_subset ?_ ?_ ?_ ?_ <;> simp

structure IsSummablePair (M N : Matroid α) (T : Set α) : Prop where
  inter_eq : M.E ∩ N.E = T
  restrict_eq_restrict : M ↾ T = N ↾ T
  isModularFlat_left : M.IsModularFlat T

attribute [grind →] IsSummablePair.inter_eq

lemma IsSummablePair.closure_inter_right (h : IsSummablePair M N T) (X : Set α) :
    M.closure X ∩ N.E = M.closure X ∩ T := by
  grind

lemma IsSummablePair.closure_inter_left (h : IsSummablePair M N T) (X : Set α) :
    N.closure X ∩ M.E = N.closure X ∩ T := by
  grind

lemma IsSummablePair.closure_union_closure_right (h : IsSummablePair M N T) :
    M.closure (X ∪ N.closure X) = M.closure (X ∪ (N.closure X ∩ T)) := by
  rw [← closure_inter_ground, union_inter_distrib_right, h.closure_inter_left,
    closure_union_congr_left (M.closure_inter_ground ..)]

lemma IsSummablePair.closure_union_closure_left (h : IsSummablePair M N T) :
    N.closure (X ∪ M.closure X) = N.closure (X ∪ (M.closure X ∩ T)) := by
  rw [← closure_inter_ground, union_inter_distrib_right, h.closure_inter_right,
    closure_union_congr_left (N.closure_inter_ground ..)]

lemma IsSummablePair.closure_inter_eq_closure (h : IsSummablePair M N T) (hX : X ⊆ T) :
    N.closure X ∩ T = M.closure X := by
  rw [← N.restrict_closure_eq hX (by grind), ← h.restrict_eq_restrict,
    M.restrict_closure_eq hX (by grind),
    inter_eq_self_of_subset_left (h.isModularFlat_left.isFlat.closure_subset_of_subset hX)]

-- lemma IsSummablePair.closure_inter_subset (h : IsSummablePair M N T) :
--     M.closure X ∩ T ⊆ M.closure X := by
--   rw [← N.closure_inter_ground]


lemma IsSummablePair.closure_subset_closure (h : IsSummablePair M N T) (hX : X ⊆ N.E) :
    M.closure X ⊆ N.closure X := by
  wlog hXT : X ⊆ T generalizing X with aux
  · grw [← closure_inter_ground, aux (by grind) (by grind), inter_subset_left]
  grw [← h.closure_inter_eq_closure hXT, inter_subset_left]

lemma IsSummablePair.isFlat_left_closure_right_inter (h : IsSummablePair M N T) (X : Set α) :
    M.IsFlat (N.closure X ∩ M.E) := by
  suffices aux : (M ↾ T).IsFlat (N.closure X ∩ M.E) by
    replace aux := aux.closure
    rwa [restrict_closure_eq _ (by grind) (by grind), inter_eq_self_of_subset_left,
      ← isFlat_iff_closure_eq] at aux
    rw [← h.isModularFlat_left.isFlat.closure]
    exact M.closure_subset_closure <| by grind
  grw [h.restrict_eq_restrict, h.closure_inter_left, isFlat_iff_subset_closure_self,
    restrict_closure_eq _ inter_subset_right (by grind), subset_inter_iff,
    and_iff_left inter_subset_right, inter_subset_left, inter_subset_left, closure_closure]

lemma IsSummablePair.closure_union_inter_subset (h : IsSummablePair M N T) (X : Set α) :
    M.closure (X ∪ N.closure X) ∩ T ⊆ N.closure (X ∪ M.closure X) := by
  grw [h.closure_union_closure_right, ← closure_union_closure_left_eq, inter_comm _ T,
    h.isModularFlat_left.distrib_of_subset_self (M.closure_isFlat ..) (by grind),
    h.closure_subset_closure (by grind), union_comm]
  refine closure_subset_closure_of_subset_closure <| union_subset ?_ ?_
  · grw [← subset_union_left, inter_subset_left]
  grw [← subset_union_right, N.subset_closure (T ∩ M.closure X) (by grind), inter_subset_right]


def biclosure (M N : Matroid α) (X : Set α) : Set α :=
  M.closure (X ∪ N.closure X) ∪ N.closure (X ∪ M.closure X)

lemma biclosure_subset_biclosure (M N : Matroid α) (hXY : X ⊆ Y) :
    biclosure M N X ⊆ biclosure M N Y := by
  grw [biclosure, hXY, ← biclosure]

lemma subset_biclosure (M N : Matroid α) (hX : X ⊆ M.E ∪ N.E) : X ⊆ biclosure M N X := by
  rw [biclosure, ← inter_eq_self_of_subset_left hX, inter_union_distrib_left]
  refine union_subset_union ?_ ?_
  · grw [← subset_union_left, ← subset_union_left, ← M.subset_closure ..]
  grw [← subset_union_left, ← subset_union_right, ← N.subset_closure ..]

lemma biclosure_subset_union_ground (M N : Matroid α) (X : Set α) :
    biclosure M N X ⊆ M.E ∪ N.E :=
  union_subset_union (closure_subset_ground ..) (closure_subset_ground ..)

lemma IsSummablePair.biclosure_inter_right_eq (h : IsSummablePair M N T) (X : Set α) :
    (biclosure M N X) ∩ N.E = N.closure (X ∪ M.closure X) := by
  grw [biclosure, union_inter_distrib_right,
    inter_eq_self_of_subset_left (N.closure_subset_ground ..), union_eq_right,
    h.closure_inter_right, h.closure_union_inter_subset]


-- lemma IsSummablePair.foo (h : IsSummablePair M N T) (X : Set α) :
--     M.closure (N.closure (X ∪ M.closure X)) ⊆ M.closure (N.closure X) := by
--   refine closure_subset_closure_of_subset_closure ?_

lemma IsSummablePair.closure_biclosure (h : IsSummablePair M N T) :
    M.closure (biclosure M N X) = (biclosure M N X) ∩ M.E := by
  refine (subset_inter ?_ (M.closure_subset_ground _)).antisymm
    <| inter_ground_subset_closure ..
  rw [biclosure, closure_union_closure_left_eq, union_assoc,
    union_eq_self_of_subset_left (N.closure_subset_closure subset_union_left),
    ← closure_union_closure_left_eq, ← M.closure_union_closure_left_eq X,
    ← N.closure_union_closure_left_eq]
  set F := M.closure X with hF
  set G := N.closure X with hG
  rw [← M.closure_inter_ground, union_inter_distrib_right,
    inter_eq_self_of_subset_left (show F ⊆ M.E from M.closure_subset_ground ..),
    h.closure_inter_left, union_comm G]
  have hmod := h.isModularFlat_left.distrib_of_subset_self (X := F) (Y := N.closure (F ∪ G) ∩ T)
    (M.closure_isFlat ..) inter_subset_right
  intro e he
  by_cases heT : e ∈ T
  · refine mem_of_mem_of_subset (hmod.subset ⟨heT, he⟩) ?_
    grw [h.closure_subset_closure (by grind), ← subset_union_right (s := M.closure (F ∪ G)),
      union_eq_self_of_subset_left, inter_subset_left, closure_closure]
    grw [subset_inter_iff, and_iff_left inter_subset_left, ← subset_union_left,
      hF, inter_comm, ← h.closure_inter_right, inter_ground_subset_closure]
  left

  have P : Set α := sorry
  have Q : Set α := sorry
  have' := h.isModularFlat_left.distrib_of_subset_self (X := P) (Y := Q)
    -- union_comm, inter_comm _ T, ← inter_self T, inter_assoc]
  -- have' := (h.isModularFlat_left.isModularPair (F := F) (M.closure_isFlat X)).distrib_of_subset_left
  --   (Y := N.closure (F ∪ G) ∩ T) (h.isModularFlat_left.isFlat) inter_subset_right

  -- have' := h.isModularFlat_left.distrib_of_subset_self (Y := N.closure (F ∪ G) ∩ T) (X := F)
  --   (closure_isFlat ..) inter_subset_right

  -- (h.isFlat_left_closure_right_inter (F ∪ G))




  -- rw [biclosure]

lemma IsSummablePair.biclosure_biclosure (h : IsSummablePair M N T) (X : Set α) :
    biclosure M N (biclosure M N X) = biclosure M N X := by
  refine subset_antisymm ?_ (subset_biclosure _ _ (biclosure_subset_union_ground ..))
  nth_rw 1 [biclosure, ← N.closure_inter_ground, h.biclosure_inter_right_eq, N.closure_closure,
    biclosure, union_assoc, union_self, ← biclosure, ← N.closure_inter_ground,
      union_inter_distrib_right, h.biclosure_inter_right_eq, N.closure_union_closure_left_eq,


      h.closure_biclosure, h.closure_biclosure, union_subset_iff,
      and_iff_right inter_subset_left, inter_right_comm, h.biclosure_inter_right_eq,
      ← closure_union_closure_left_eq, union_eq_self_of_subset_right inter_subset_left,
      closure_closure]
  exact subset_union_right








structure IsFlatPair (M N : Matroid α) (F₀ F₁ : Set α) where
  isFlat_left : M.IsFlat F₀
  isFlat_right : N.IsFlat F₁
  subset_right : F₀ ∩ N.E ⊆ F₁
  subset_left : F₁ ∩ M.E ⊆ F₀

lemma IsFlatPair.symm (h : IsFlatPair M N F₀ F₁) : IsFlatPair N M F₁ F₀ :=
  ⟨h.isFlat_right, h.isFlat_left, h.subset_left, h.subset_right⟩

@[grind →]
lemma IsFlatPair.subset_ground_left (h : IsFlatPair M N F₀ F₁) : F₀ ⊆ M.E :=
  h.isFlat_left.subset_ground

@[grind →]
lemma IsFlatPair.subset_ground_right (h : IsFlatPair M N F₀ F₁) : F₁ ⊆ N.E :=
  h.isFlat_right.subset_ground

lemma IsFlatPair.union_inter_ground_left (h : IsFlatPair M N F₀ F₁) : (F₀ ∪ F₁) ∩ M.E = F₀ := by
  rw [union_inter_distrib_right, inter_eq_self_of_subset_left h.subset_ground_left,
    union_eq_self_of_subset_right h.subset_left]

lemma IsFlatPair.union_inter_ground_right (h : IsFlatPair M N F₀ F₁) : (F₀ ∪ F₁) ∩ N.E = F₁ := by
  rw [union_inter_distrib_right, inter_eq_self_of_subset_left h.subset_ground_right,
    union_eq_self_of_subset_left h.subset_right]

attribute [grind →] IsFlatPair.isFlat_left IsFlatPair.isFlat_right

lemma IsSummablePair.isFlatPair (h : IsSummablePair M N T) (hF₀ : M.IsFlat F₀) (X : Set α) :
    IsFlatPair M N (M.closure (F₀ ∪ N.closure (F₀ ∪ X))) (N.closure (F₀ ∪ X)) := by
  refine ⟨by simp, by simp, ?_, ?_⟩
  · grw [h.closure_inter_right, ← closure_inter_ground, union_inter_distrib_right,
      inter_eq_self_of_subset_left hF₀.subset_ground, h.closure_inter_left, inter_comm,
      h.isModularFlat_left.distrib_of_subset_self hF₀ (Y := N.closure (F₀ ∪ X) ∩ T)
      inter_subset_right, h.closure_subset_closure (by grind)]
    refine N.closure_subset_closure_of_subset_closure <| union_subset ?_ inter_subset_left
    exact subset_closure_of_subset' _ (by grind) (by grind)
  grw [← subset_union_right (t := N.closure (F₀ ∪ X)),
    ← M.subset_closure_of_subset' inter_subset_left inter_subset_right]

def IsSumFlat (M N : Matroid α) (F : Set α) : Prop :=
  ∃ F₀ F₁, IsFlatPair M N F₀ F₁ ∧ F₀ ∪ F₁ = F

lemma IsSumFlat.symm (h : IsSumFlat M N F) : IsSumFlat N M F := by
  obtain ⟨F₀, F₁, h, rfl⟩ := h
  exact ⟨F₁, F₀, h.symm, union_comm ..⟩

lemma IsFlatPair.isSumFlat_union (h : IsFlatPair M N F₀ F₁) : IsSumFlat M N (F₀ ∪ F₁) :=
  ⟨_, _, h, rfl⟩

-- /-- If `F` is a sum flat containing the flat `F₀` on the LHS and the set `X` on the RHS,
-- then it must contain a bunch of other stuff. -/
-- lemma IsSumFlat.subset_of_subset_subset (h : M.IsSumFlat N F) (hF₀ : M.IsFlat F₀) (hF₀F : F₀ ⊆ F)
--     (hX : X ⊆ N.E) (hXF : X ⊆ F) :
--     M.closure (F₀ ∪ N.closure (F₀ ∪ X)) ∪ N.closure (F₀ ∪ X) ⊆ F := by
--   obtain ⟨K₀, K₁, hK, rfl⟩ := h
--   have h₀ : F₀ ⊆ K₀ := by
--     rwa [← hK.union_inter_ground_left, subset_inter_iff, and_iff_left hF₀.subset_ground]
--   have hss : N.closure (F₀ ∪ X) ⊆ K₁ := by
--     grw [← closure_inter_ground, union_inter_distrib_right, inter_eq_self_of_subset_left hX]
--     refine hK.isFlat_right.closure_subset_of_subset <| union_subset ?_ ?_
--     · grw [h₀, ← hK.union_inter_ground_right, ← subset_union_left]
--     grw [← hK.union_inter_ground_right, subset_inter_iff, and_iff_left hX, hXF]
--   refine union_subset_union ?_ hss
--   nth_grw 1 [h₀, hss, ← closure_inter_ground, hK.union_inter_ground_left, hK.isFlat_left.closure]

-- lemma IsSumFlat.subset_of_subset_subset' (h : M.IsSumFlat N F) (hXF : X ⊆ F) (hYF : Y ⊆ F) :
--     M.closure (X ∪ N.closure (X ∪ Y)) ⊆ F := by
--   obtain ⟨K₀, K₁, hK, rfl⟩ := h
--   grw [← subset_union_left (s := K₀), hXF, ← closure_inter_ground, union_inter_distrib_right,
--     hK.union_inter_ground_left, union_eq_self_of_subset_right hYF,
--       ← N.closure_inter_ground, hK.union_inter_ground_right, hK.isFlat_right.closure,
--       ← inter_eq_self_of_subset_left hK.subset_ground_left, ← union_inter_distrib_right,
--       hK.union_inter_ground_left, hK.isFlat_left.closure,
--       inter_eq_self_of_subset_left hK.subset_ground_left]

lemma IsSumFlat.subset_of_subset_subset (h : M.IsSumFlat N F) (hXF : X ⊆ F) :
    M.closure (X ∪ N.closure X) ⊆ F := by
  obtain ⟨K₀, K₁, hK, rfl⟩ := h
  grw [hXF, ← N.closure_inter_ground, hK.union_inter_ground_right, hK.isFlat_right.closure,
    union_assoc, union_self, ← closure_inter_ground, hK.union_inter_ground_left,
    hK.isFlat_left.closure, ← subset_union_left]

lemma foo (h : IsSummablePair M N T) (h : IsSumFlat M N F) (he : e ∈ M.E) (heF₀ : e ∉ F) :
    ∃ (F' : Set α), e ∈ F' ∧ Minimal (fun X ↦ F ⊂ X ∧ IsSumFlat M N X) F' := by
  obtain ⟨F₀, F₁, hF₀F₁, rfl⟩ := h

  -- have h' := h.isFlatPair (M.closure_isFlat (insert e F₀)) F₁
  -- rw [closure_union_closure_left_eq] at h'

  set F₀e := M.closure (insert e F₀) with hF₀e
  have hF₀e_flat : M.IsFlat F₀e := closure_isFlat ..
  set F₀' := M.closure (F₀e ∪ N.closure (F₀e ∪ F₁)) with hF₀'
  set F₁' := N.closure (F₀e ∪ F₁) with hF₁'
  -- set F' := F₀' ∪ F₁' with hF'
  have hFp : IsFlatPair M N F₀' F₁' := h.isFlatPair hF₀e_flat F₁
  have heF' : e ∈ F₀' ∪ F₁' := by
    grw [← subset_union_left, hF₀', hF₀e, ← subset_union_left, closure_closure]
    exact M.mem_closure_of_mem' (by simp) he
  have hssu : F₀ ∪ F₁ ⊂ F₀' ∪ F₁' := sorry
  refine ⟨F₀' ∪ F₁', heF', minimal_iff_forall_ssubset.2 ⟨⟨hssu, hFp.isSumFlat_union⟩, ?_⟩⟩
  rintro _ hKss ⟨hssK, K₀, K₁, hK, rfl⟩
  have hFK₀ : F₀ ⊆ K₀ := by
    grw [← hK.union_inter_ground_left, subset_inter_iff, and_iff_left hF₀F₁.subset_ground_left,
      ← hssK, ← subset_union_left]

  by_cases heK₀ : e ∈ K₀
  · refine hKss.not_subset <| union_subset ?_ ?_
    · grw [← hK.isSumFlat_union.subset_of_subset_subset (X := insert e (F₀ ∪ F₁)) (by grind),
        ← subset_union_left, hF₀', ← closure_inter_ground,
        closure_subset_closure_iff_subset_closure, union_inter_distrib_right,
        inter_eq_self_of_subset_left (by grind), union_subset_iff, hF₀e,
        and_iff_right (closure_subset_closure _ (by grind))]

      -- show K₀ = M.closure (insert e K₀) by rw [insert_eq_of_mem heK₀, hK.isFlat_left.closure],
      -- ← hK.isFlat_right.closure,
      -- insert_union]
    have hss₀ : F₀' ⊆ K₀ := by
      -- rw [← hK.union_inter_ground_left, subset_inter_iff, and_iff_left (by grind), ]
      grw [hF₀', hF₁', ← closure_inter_ground, hK.isFlat_left.closure_subset_iff_subset (by grind),
        union_inter_distrib_right, union_subset_iff,
        inter_eq_self_of_subset_left hF₀e_flat.subset_ground, hF₀e,
        hK.isFlat_left.closure_subset_iff_subset (by grind), and_iff_right (by grind),
        ← hK.union_inter_ground_left, ← insert_eq_self.2 heK₀, insert_union, ← hssK]
    have h₀' := hK.isSumFlat_union.subset_of_subset_subset (X := insert e F₀) (by grind)
    have h₁' := union_comm K₀ _ ▸ hK.symm.isSumFlat_union.subset_of_subset_subset
      (X := F₁) (by grind)

    refine (h'.trans_ssubset hKss).not_subset ?_
    rw [hF₀', hF₁', hF₀e]

  -- -- set F₀' := M.closure (insert e F₀) with hF₀'
  -- -- set F' := M.closure (insert e F₀ ∪ N.closure (F₀e ∪ F₁)) ∪ N.closure (F₀e ∪ F₁) with hF'
  -- have heF' : e ∈ F' := .inl <| M.mem_closure_of_mem' (by simp [hF₀e]) he
  -- have hssu : F₀ ∪ F₁ ⊂ F' := by
  --   refine (union_subset_union ?_ ?_).ssubset_of_mem_notMem heF' heF₀
  --   · grw [hF₀', ← subset_union_left, hF₀e, ← subset_insert, hF₀F₁.isFlat_left.closure]
  --   grw [hF₁', ← subset_union_right, hF₀F₁.isFlat_right.closure]
  -- have := h'.isSumFlat_union
  -- simp_rw [minimal_iff_forall_ssubset]
  -- refine ⟨F', heF', ⟨hssu, ?_⟩, fun X hXF' ⟨hXssu, hXsf⟩ ↦ ?_⟩
  -- · rw [hF', hF₀', hF₁']
  -- obtain ⟨K₀, K₁, hK, rfl⟩ := hXsf
  -- by_cases heK₀ : e ∈ K₀
  -- · have h₀ : F₀' ⊆ K₀ := by
  --     grw [hF₀', hK.isFlat_left.closure_subset_iff_subset (by grind), insert_subset_iff,
  --       and_iff_right heK₀, ← hK.union_inter_ground_left, ← hF₀F₁.union_inter_ground_left,
  --       hXssu]

    -- have h₁ : F₁' ⊆ K₀ := by



  -- refine ⟨_, ?_, minimal_iff_forall_ssubset.2 ⟨⟨?_, h'.isSumFlat_union⟩, ?_⟩⟩

  -- have := hN.isModularPair.inter_closure_eq
  -- -- have hmod := (hN _ (N.closure_isFlat (F₁ ∪ M.closure (insert e F₀)))).inter_closure_eq
  -- rw [closure_closure] at hmod
  -- grw [← inter_eq_self_of_subset_left (N.closure_subset_ground _), inter_assoc, inter_comm N.E,
  --   N.subset_closure (M.E ∩ N.E), ← hmod]
  -- have hmod' := (hN F₁ h.isFlat_right).inter_closure_eq
  -- rw [← inter_assoc, closure_inter_ground] at hmod

    -- have := h.subset_right

-- lemma foo (hM : M.IsFlat F₀) (hN : N.IsFlat F₁) (hF₀F₁ : F₁ ∩ M.E ⊆ F₀) (heM : e ∈ M.E) (heN : e ∉ N.E) (heF₀ : e ∉ F₀) :
--     N.closure (F₁ ∪ (M.closure (insert e F₀) ∩ N.E)) ∩ M.E ⊆ M.closure (insert e F₀)

-- lemma sumFlat'_iInter (M N : Matroid α) [Nonempty ι] (F₀ F₁ F : ι → Set α)
--     (h : ∀ i, SumFlat' M N (F₀ i) (F₁ i) (F i)) :
--     SumFlat' M N (⋂ i, F₀ i) (⋂ i, F₁ i) (⋂ i, F i) := by
--   refine ⟨IsFlat.iInter (fun i ↦ (h i).isFlat_left), IsFlat.iInter (fun i ↦ (h i).isFlat_right),
--     ?_, ?_, ?_⟩
--   · rw [iInter_inter, iInter_congr fun i ↦ (h i).inter_left]
--   · rw [iInter_inter, iInter_congr fun i ↦ (h i).inter_right]
--   obtain i : ι := Classical.ofNonempty
--   grw [← iInter_congr (fun i ↦ (h i).inter_left), ← iInter_congr (fun i ↦ (h i).inter_right),
--     ← iInter_inter, ← iInter_inter, ← inter_union_distrib_left, inter_eq_left,
--     iInter_subset _ i, ← (h i).union_eq]
--   exact union_subset_union (h i).isFlat_left.subset_ground (h i).isFlat_right.subset_ground

-- lemma SumFlat'.bar_left (hF : SumFlat' M N F₀ F₁ F) (heM : e ∈ M.E) (he : e ∉ N.E) (heF : e ∉ F₀) :
--   SumFlat M N (M.closure (insert e F₀)) (N.closure (F₁ ∪ (M.closure (insert e F₀) ∩ N.E)))

-- lemma sumFlat_ground (M N : Matroid α) : SumFlat M N (M.E ∪ N.E) := by
--   refine ⟨?_, ?_, rfl.subset⟩
--   · rw [inter_eq_self_of_subset_right subset_union_left]
--     exact M.ground_isFlat
--   rw [inter_eq_self_of_subset_right subset_union_right]
--   exact N.ground_isFlat

-- lemma sumFlat_iInter [Nonempty ι] (F : ι → Set α) (hFs : ∀ i, SumFlat M N (F i)) :
--     SumFlat M N <| (⋂ i, F i) := by
--   refine ⟨?_, ?_, ?_⟩
--   · rw [iInter_inter]
--     exact IsFlat.iInter fun i ↦ (hFs i).isFlat_left
--   · rw [iInter_inter]
--     exact IsFlat.iInter fun i ↦ (hFs i).isFlat_right
--   sorry


-- lemma SumFlat.inter (hF : SumFlat M N F) (hF' : SumFlat M N F') :
--     SumFlat M N (F ∩ F') := sorry

-- -- @[simp]
-- lemma sumFlat_closure_union_closure (hX : M.closure X ∩ N.E ⊆ N.closure Y)
--     (hY : N.closure Y ∩ M.E ⊆ M.closure X) : SumFlat M N (M.closure X ∪ N.closure Y) := by
--   refine ⟨?_, ?_, union_subset_union (closure_subset_ground ..) (closure_subset_ground ..)⟩
--   · rw [union_inter_distrib_right, union_eq_self_of_subset_right (by grind),
--       inter_eq_self_of_subset_left (M.closure_subset_ground ..)]
--     exact M.closure_isFlat ..
--   rw [union_inter_distrib_right, inter_eq_self_of_subset_left (N.closure_subset_ground ..),
--     union_eq_self_of_subset_left hX]
--   exact N.closure_isFlat ..


-- lemma SumFlat.bar_left (hF : SumFlat M N F) (heM : e ∈ M.E) (he : e ∉ N.E) (heF : e ∉ F) :
--   SumFlat M N (M.closure (insert e (F ∩ M.E)) ∪ N.closure (F ∩ N.E ∪ N.closure ((insert e (F ∩ M.E)))))

-- lemma SumFlat.foo_left (hF : SumFlat M N F) (heM : e ∈ M.E) (he : e ∉ N.E) (heF : e ∉ F) :
--     ∃ F', SumFlat M N F' ∧ e ∈ F' ∧ Minimal (fun X ↦ F ⊂ X ∧ SumFlat M N X) F' := by
--   have hsf : SumFlat M N
--       (M.closure (insert e (F ∩ M.E)) ∪ N.closure ((F ∩ M.closure (F ∩ M.E ∩ N.E)) ∩ N.E)) := by
--     refine sumFlat_closure_union_closure ?_ ?_
--   refine ⟨_, hsf,
--     .inl (mem_closure_of_mem' _ (mem_insert ..) he), minimal_iff_forall_ssubset.2
--     ⟨⟨?_, hsf⟩, ?_⟩⟩

--   · sorry
--   sorry





-- lemma SumFlat.foo (hF : SumFlat M N F) (he : e ∈ M.E ∪ N.E) (heF : e ∉ F) :
--     ∃! F', SumFlat M N F' ∧ e ∈ F' ∧ Minimal (fun X ↦ F ⊂ X ∧ SumFlat M N X) F' := by
--   sorry

--     -- rw [inter_assoc, inter_eq_self_of_subset_right subset_union_left]
--     -- have := IsFlat.iInter_inter_ground (M := M) (Fs := fun (F : Fs) ↦ F.1 ∩ M.E)
--     --   (fun F ↦ (hFs F.1 F.2).isFlat_left)
--     -- simp only [iInter_coe_set] at this
--     -- rw [biInter_inter] at this
