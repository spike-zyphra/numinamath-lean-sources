import Mathlib

theorem algebra_275099 :
    Set.ncard {k : ℤ | ∃ x : ℝ, -1/8 * x^2 + 4 = x^2 - k ∧ x^2 - k ≥ 0} = 37 := by
  have h1 : {k : ℤ | ∃ x : ℝ, -1/8 * x^2 + 4 = x^2 - k ∧ x^2 - k ≥ 0} = Set.Icc (-4 : ℤ) 32 := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- Assume k is in the set
      rintro ⟨x, heq, hge⟩
      have h2 : (9 : ℝ) * x^2 = 32 + 8 * (k : ℝ) := by
        nlinarith
      have h3 : (k : ℝ) ≤ (32 : ℝ) := by
        nlinarith [sq_nonneg x, h2, hge]
      have h4 : k ≤ 32 := by
        by_contra h
        push_neg at h
        have h5 : (k : ℝ) > (32 : ℝ) := by
          exact_mod_cast h
        linarith
      have h5 : (k : ℝ) ≥ (-4 : ℝ) := by
        nlinarith [sq_nonneg x, h2]
      have h6 : k ≥ (-4 : ℤ) := by
        by_contra h
        push_neg at h
        have h7 : (k : ℝ) < (-4 : ℝ) := by
          exact_mod_cast h
        linarith
      exact ⟨h6, h4⟩
    · -- Assume k is in the interval [-4, 32]
      rintro ⟨hk1, hk2⟩
      have h7 : 32 + 8 * (k : ℝ) ≥ 0 := by
        have hk8 : (k : ℝ) ≥ (-4 : ℝ) := by
          exact_mod_cast hk1
        nlinarith
      use Real.sqrt ((32 + 8 * (k : ℝ)) / 9)
      constructor
      · -- Show that: -1/8 * x^2 + 4 = x^2 - k
        field_simp at *
        nlinarith [Real.sqrt_nonneg ((32 + 8 * (k : ℝ)) / 9), Real.sq_sqrt (show (0 : ℝ) ≤ (32 + 8 * (k : ℝ)) / 9 by nlinarith)]
      · -- Show that: x^2 - k ≥ 0
        have h9 : (32 + 8 * (k : ℝ)) ≥ (9 * (k : ℝ)) := by
          have hk10 : (k : ℝ) ≤ (32 : ℝ) := by
            exact_mod_cast hk2
          nlinarith
        have h10 : (Real.sqrt ((32 + 8 * (k : ℝ)) / 9) ) ^ 2 ≥ (k : ℝ) := by
          nlinarith [Real.sqrt_nonneg ((32 + 8 * (k : ℝ)) / 9), Real.sq_sqrt (show (0 : ℝ) ≤ (32 + 8 * (k : ℝ)) / 9 by nlinarith)]
        linarith [h10, show (k : ℝ) ≥ (-4 : ℝ) from by exact_mod_cast hk1]
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  native_decide