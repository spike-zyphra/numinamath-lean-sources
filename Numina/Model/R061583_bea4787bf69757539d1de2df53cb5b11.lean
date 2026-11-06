import Mathlib

theorem algebra_97793 : ∑ᶠ x ∈ {x : ℝ | |x ^ 2 - 12 * x + 34| = 2}, x = 18 := by

  have h1 : {x : ℝ | |x ^ 2 - 12 * x + 34| = 2} = {4, 6, 8} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume |x^2 - 12x + 34| = 2, prove x ∈ {4, 6, 8}
      intro h
      cases eq_or_eq_neg_of_abs_eq h with
      | inl h1 =>
        -- Case where x^2 - 12x + 34 = 2
        have h2 : x ^ 2 - 12 * x + 32 = 0 := by linarith
        have : (x - 4) * (x - 8) = 0 := by
          nlinarith
        cases' (mul_eq_zero.1 this) with h4 h8
        · -- Case x - 4 = 0, so x = 4
          left
          linarith
        · -- Case x - 8 = 0, so x = 8
          right
          right
          linarith
      | inr h2 =>
        -- Case where x^2 - 12 x + 34 = -2
        have h3 : x ^ 2 - 12 * x + 36 = 0 := by linarith
        have : (x - 6) ^ 2 = 0 := by
          nlinarith
        have h6 : x - 6 = 0 := by
          apply pow_eq_zero 
          exact this
        have hx : x = 6 := by linarith
        right
        left
        linarith
    · -- Assume x ∈ {4, 6, 8}, prove |x^2 - 12 x + 34| = 2
      rintro (rfl | rfl | rfl)
      · -- Case x = 4
        norm_num
      · -- Case x = 6
        norm_num
      · -- Case x = 8
        norm_num
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  <;> norm_num <;> linarith