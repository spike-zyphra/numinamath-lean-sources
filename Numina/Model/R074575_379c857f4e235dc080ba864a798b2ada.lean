import Mathlib

theorem algebra_6385 : ∑ᶠ x ∈ {x : ℤ | x + 1 ≠ 0 ∧ x + 2 ≠ 0 ∧ x + 5 ≠ 0 ∧ (1 / (x + 1 : ℝ) - 1 / (x + 2 : ℝ)) * (x + 5 : ℝ) = 1}, x = -2 := by

  have h1 : {x : ℤ | x + 1 ≠ 0 ∧ x + 2 ≠ 0 ∧ x + 5 ≠ 0 ∧ (1 / (x + 1 : ℝ) - 1 / (x + 2 : ℝ)) * (x + 5 : ℝ) = 1} = {(-3 : ℤ), (1 : ℤ)} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume x is in the solution set
      intro h
      rcases h with ⟨h1, h2, h3, heq⟩
      field_simp [show (x + 1 : ℝ) ≠ 0 by exact_mod_cast h1, show (x + 2 : ℝ) ≠ 0 by exact_mod_cast h2, show (x + 5 : ℝ) ≠ 0 by exact_mod_cast h3] at heq
      ring_nf at heq
      have h4 : (x : ℝ) ^ 2 + 2 * (x : ℝ) - 3 = 0 := by
        nlinarith
      have h5 : x ^ 2 + 2 * x - 3 = 0 := by
        have h5 : (x : ℝ) ^ 2 + 2 * (x : ℝ) - 3 = 0 := by
          linarith
        exact_mod_cast h5
      have : (x + 3) * (x - 1) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp this) with h6 h7
      · -- x + 3 = 0 so x = -3
        have : x = -3 := by linarith
        left
        exact this
      · -- x - 1 = 0 so x = 1
        have : x = 1 := by linarith
        right
        exact this
    · -- Show that both elements in the singleton set are in the solution set
      rintro (rfl | rfl)
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Check equation
          norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Check equation
          norm_num

  rw [h1]
  rw [finsum_mem_pair]
  all_goals norm_num