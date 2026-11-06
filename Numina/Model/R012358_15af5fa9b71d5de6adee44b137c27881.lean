import Mathlib

theorem algebra_307335 (a : ℝ) (h : ∃ x y, x ≠ y ∧ x^2 - x + a = 0 ∧ y^2 - y + a = 0 ∧ |x| + |y| ≤ 5) :
    -6 ≤ a ∧ a < 1 / 4 := by 
  rcases h with ⟨x, y, h_ne, hx, hy, h_sum⟩
  have h_sub : (x - y) * (x + y - 1) = 0 := by 
    have eq1 : x^2 - x + a = 0 := hx
    have eq2 : y^2 - y + a = 0 := hy
    have eq3 : x^2 - x - (y^2 - y) = 0 := by linarith [eq1, eq2]
    nlinarith
  cases (mul_eq_zero.mp h_sub) with
  | inl h1 =>
    exfalso
    apply h_ne 
    linarith
  | inr h2 =>
    have h_sum_eq : x + y = 1 := by linarith 
    by_cases h1 : x ≥ 0 
    · -- x ≥ 0 
      by_cases h2 : y ≥ 0 
      · -- y ≥ 0 
        have h3 : |x| + |y| = x + y := by 
          rw [abs_of_nonneg (show x ≥ 0 by linarith), abs_of_nonneg (show y ≥ 0 by linarith)]
          all_goals linarith 
        have h7 : x + y = 1 := by linarith
        constructor 
        · -- Show that -6 ≤ a 
          nlinarith 
        · -- Show that a < 1 / 4 
          nlinarith [sq_pos_of_ne_zero (show (x - y) ≠ 0 by 
            intro h'
            apply h_ne 
            linarith 
          ), sq_nonneg (x - y)]
      · -- y < 0 
        have h2 : y < 0 := by linarith 
        have h3 : |x| + |y| = x - y := by 
          rw [abs_of_nonneg (show x ≥ 0 by linarith), abs_of_neg (show y < 0 by linarith)]
          all_goals linarith 
        have h5 : x - y ≤ 5 := by 
          nlinarith [h3, h_sum]
        have h6 : x - y ≥ -5 := by
          cases abs_cases (x - y) with 
          | inl h7 => 
            nlinarith 
          | inr h7 => 
            nlinarith
        constructor
        · -- Show that -6 ≤ a 
          nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1)]
        · -- Show that a < 1 / 4 
          nlinarith [sq_pos_of_ne_zero (show (x - y) ≠ 0 by 
            intro h'
            apply h_ne 
            linarith 
          ), sq_nonneg (x - y)]
    · -- x < 0 
      have h1 : x < 0 := by linarith 
      by_cases h2 : y ≥ 0 
      · -- y ≥ 0 
        have h3 : |x| + |y| = -x + y := by 
          rw [abs_of_neg (show x < 0 by linarith), abs_of_nonneg (show y ≥ 0 by linarith)]
          all_goals linarith 
        have h6 : -x + y ≤ 5 := by 
          nlinarith [h3, h_sum]
        have h7 : -x + y ≥ -5 := by 
          cases abs_cases (x - y) with 
          | inl h7 => 
            nlinarith 
          | inr h7 => 
            nlinarith 
        constructor
        · -- Show that -6 ≤ a 
          nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1)]
        · -- Show that a < 1 / 4 
          nlinarith [sq_pos_of_ne_zero (show (x - y) ≠ 0 by 
            intro h'
            apply h_ne 
            linarith 
          ), sq_nonneg (x - y)]
      · -- y < 0 
        have h2 : y < 0 := by linarith 
        have h3 : |x| + |y| = -x - y := by 
          rw [abs_of_neg (show x < 0 by linarith), abs_of_neg (show y < 0 by linarith)]
          all_goals linarith 
        have h7 : -x - y ≤ 5 := by 
          nlinarith [h3, h_sum]
        have h6 : -x - y ≥ -5 := by
          cases abs_cases (x - y) with 
          | inl h7 => 
            nlinarith 
          | inr h7 => 
            nlinarith
        constructor 
        · -- Show that -6 ≤ a 
          nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1)]
        · -- Show that a < 1 / 4 
          nlinarith [sq_pos_of_ne_zero (show (x - y) ≠ 0 by 
            intro h'
            apply h_ne 
            linarith 
          ), sq_nonneg (x - y)]