import Mathlib

theorem algebra_290567 (y : ℝ) :
    3 * y ≥ 3 ↔ ∃ x, 3 * y = abs (x + 1) + Real.sqrt ((x - 2) ^ 2) := by
  constructor
  · -- First direction: if 3 * y ≥ 3, then there exists an x such that 3 * y = abs (x + 1) + √((x - 2) ^ 2)
    intro hy
    by_cases h : 3 * y > 3
    · -- Case y > 1
      use (1 - 3 * y) / 2
      have h1 : Real.sqrt (( (1 - 3 * y) / 2 - 2 ) ^ 2) = abs ( (1 - 3 * y) / 2 - 2 ) := by
        rw [Real.sqrt_sq_eq_abs]
      rw [h1]
      have h2 : abs ((1 - 3 * y) / 2 + 1) = (3 * (y - 1)) / 2 := by
        have h3 : (1 - 3 * y) / 2 + 1 = (3 - 3 * y) / 2 := by
          linarith
        rw [h3]
        have h4 : (3 - 3 * y : ℝ) / 2 < 0 := by
          nlinarith
        rw [abs_of_neg h4]
        all_goals linarith
      have h3 : abs (( (1 - 3 * y) / 2 - 2 ) ) = (3 * y + 3) / 2 := by
        have h4 : ( (1 - 3 * y) / 2 - 2 : ℝ) < 0 := by
          nlinarith
        rw [abs_of_neg h4]
        linarith
      rw [h2, h3]
      linarith
    · -- Case 3 * y = 3
      have h_eq : 3 * y = 3 := by
        nlinarith
      use (0 : ℝ)
      rw [h_eq]
      have h1 : Real.sqrt ((0 - 2 : ℝ) ^ 2) = abs (0 - 2 : ℝ) := by
        rw [Real.sqrt_sq_eq_abs]
      rw [h1]
      norm_num [abs_of_nonneg, abs_of_nonpos]
  · -- Second direction: if there exists an x such that 3 * y = abs (x + 1) + √((x - 2) ^ 2), then 3 * y ≥ 3
    rintro ⟨x, hx⟩
    have h1 : Real.sqrt ((x - 2) ^ 2) = abs (x - 2) := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h1] at hx
    have h2 : abs (x + 1) + abs (x - 2) ≥ 3 := by
      cases' abs_cases (x + 1) with h1 h1 <;> 
      cases' abs_cases (x - 2) with h2 h2 <;> 
      linarith
    linarith [h2, hx]