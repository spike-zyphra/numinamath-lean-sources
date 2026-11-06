import Mathlib

theorem algebra_300041 (m : ℝ) :
  {x : ℝ | abs (1 - abs x) = m - 2008}.encard = 2
  ↔ (m = 2008 ∨ m > 2009) := by

  have h_set0: m < 2008 → {x : ℝ | abs (1 - abs x) = m - 2008} = ∅ := by
    intro hm
    ext x
    simp
    have : abs (1 - |x|) ≥ 0 := by positivity
    linarith

  have h_set4: 2008<m ∧ m≤2009 → {x : ℝ | abs (1 - abs x) = m - 2008} = {2007 - m, 2009 - m, -2009 + m, -2007 + m} := by
    intro ⟨hm1, hm2⟩
    ext x
    simp
    constructor
    . intro hx
      rw [abs_eq (by linarith)] at hx
      rcases hx with hx | hx
      . have : |x| = 2009-m := by linarith
        rw [abs_eq (by linarith)] at this
        rcases this with hx | hx
        . right; left; linarith
        . right; right; left; linarith

      . have : |x| = m-2007 := by linarith
        rw [abs_eq (by linarith)] at this
        rcases this with hx | hx
        . right; right; right; linarith
        . left; linarith

    . intro hx

      rcases hx with rfl | rfl | rfl | rfl
      . nth_rw 2 [abs_of_neg (by linarith)]
        rw [abs_of_nonpos (by linarith)]
        ring_nf

      . nth_rw 2 [abs_of_nonneg (by linarith)]
        rw [abs_of_nonneg (by linarith)]
        ring_nf

      . nth_rw 2 [abs_of_nonpos (by linarith)]
        rw [abs_of_nonneg (by linarith)]
        ring_nf

      . nth_rw 2 [abs_of_pos (by linarith)]
        rw [abs_of_nonpos (by linarith)]
        ring_nf

  constructor
  . intro hx
    by_contra hm1
    simp at hm1
    obtain ⟨hm1, hm2⟩ := hm1
    rcases lt_trichotomy m 2008 with hm3 | hm4 | hm5
    . have := h_set0 hm3
      rw [this] at hx
      simp at hx
    . tauto
    . have := h_set4 ⟨hm5, hm2⟩
      rw [this] at hx

      by_cases hm : m = 2009
      . subst m
        norm_num at hx
        rw [Set.encard_insert_of_not_mem] at hx
        rw [Set.encard_pair] at hx
        norm_num at hx
        norm_num
        by_contra h_contra
        rcases h_contra with h | h
        all_goals norm_num at h
      . repeat rw [Set.encard_insert_of_not_mem] at hx
        simp at hx
        norm_num at hx
        all_goals simp
        . by_contra h_contra
          simp at h_contra
          have : ¬2009 - m = -2009 + m := by
            by_contra h
            have : m = 2009 := by linarith
            subst m
            norm_num at hm
          have := h_contra this
          have : m = 2008 := by linarith
          subst m
          norm_num at hm1
        . by_contra h_contra
          simp at h_contra
          have : ¬2007 - m = -2009 + m := by
            by_contra h
            have : m = 2009 := by linarith
            subst m
            norm_num at hm
          have := h_contra this
          have : m = 2007 := by linarith
          subst m
          norm_num at hm5

  . intro hm
    rcases hm with rfl | hm
    . norm_num
      have : {x:ℝ | 1 - |x| = 0} = {-1, 1} := by
        ext x
        simp only [Set.mem_setOf_eq]
        constructor
        . intro h
          simp at h
          have : |x| = 1 := by linarith
          simp
          suffices x = 1 ∨ x = -1 by exact this.symm
          rw [← abs_eq_abs]
          simp
          assumption

        . intro h
          rcases h with rfl | rfl
          . simp
          . simp

      rw [this]
      rw [Set.encard_pair]
      norm_num

    . have : {x: ℝ | abs (1 - |x|) = m - 2008} = {m - 2007, -m + 2007} := by
        ext x
        simp only [Set.mem_setOf_eq]
        constructor
        . intro hx
          rw [abs_eq (by linarith)] at hx
          rcases hx with hx | hx
          . have : |x| ≥ 0 := by positivity
            linarith
          . have : |x| = m - 2007 := by linarith
            rw [abs_eq (by linarith)] at this
            rcases this with hx | hx
            . left; assumption
            . right; simp; linarith

        . intro h
          rcases h with rfl | rfl
          . nth_rw 2 [abs_of_pos (by linarith)]
            rw [abs_of_nonpos (by linarith)]
            ring_nf

          . nth_rw 2 [abs_of_neg (by linarith)]
            rw [abs_of_nonpos (by linarith)]
            ring_nf

      rw [this]
      rw [Set.encard_pair]
      by_contra
      have : m = -2008 := by linarith
      rw [this] at hm
      norm_cast at hm
