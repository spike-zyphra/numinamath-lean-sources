import Mathlib

/- 2.11. Solve the equation


$$

3 \sqrt{x^{2}-9}+4 \sqrt{x^{2}-16}+5 \sqrt{x^{2}-25}=\frac{120}{x}

$$
 -/
theorem algebra_222948 (x : ℝ) (hx : x ≠ 0) :
    3 * Real.sqrt (x^2 - 9) + 4 * Real.sqrt (x^2 - 16) + 5 * Real.sqrt (x^2 - 25) =
    120 / x ↔ x = 5 := by
  constructor
  . intro h
    -- First, note that if x < 0, then the left-hand side is nonnegative, while the right-hand side
    -- is negative, so x must be positive.
    have hpos : x > 0 := by
      rcases lt_trichotomy x 0 with (hlt | heq | hgt)
      . exfalso
        have : 3 * Real.sqrt (x^2 - 9) + 4 * Real.sqrt (x^2 - 16) + 5 * Real.sqrt (x^2 - 25) ≥ 0 := by
          refine add_nonneg (add_nonneg ?_ ?_) ?_
          all_goals exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
        have : 120 / x < 0 := by
          simp [div_lt_iff_of_neg hlt]
        linarith
      . exfalso
        exact hx heq
      . exact hgt
    -- We split by cases: x < 5, x = 5, and x > 5, and show that cases other than
    -- x = 5 lead to contradictions.
    rcases lt_trichotomy x 5 with (hlt | heq | hgt)
    . exfalso
      have : 24 < 120 / x := by
        rw [lt_div_iff₀ hpos]
        refine lt_of_lt_of_le ?_ (show 24 * 5 ≤ (120 : ℝ) by norm_num)
        exact mul_lt_mul_of_pos_left hlt (by norm_num)
      have : 3 * Real.sqrt (x^2 - 9) + 4 * Real.sqrt (x^2 - 16) + 5 * Real.sqrt (x^2 - 25) < 24 := by
        rw [show (24 : ℝ) = 12 + 12 + 0 by norm_num]
        refine add_lt_add_of_lt_of_le (add_lt_add ?_ ?_) ?_
        . rw [← lt_div_iff₀' (by norm_num), Real.sqrt_lt' (by norm_num)]
          nlinarith
        . rw [← lt_div_iff₀' (by norm_num), Real.sqrt_lt' (by norm_num)]
          nlinarith
        . rw [← le_div_iff₀' (by norm_num), Real.sqrt_le_left (by norm_num)]
          nlinarith
      linarith
    . exact heq
    . exfalso
      have : 120 / x < 24 := by
        rw [div_lt_iff₀ hpos]
        refine lt_of_le_of_lt (show (120 : ℝ) ≤ 24 * 5 by norm_num) ?_
        exact mul_lt_mul_of_pos_left hgt (by norm_num)
      have : 3 * Real.sqrt (x^2 - 9) + 4 * Real.sqrt (x^2 - 16) + 5 * Real.sqrt (x^2 - 25) > 24 := by
        rw [show (24 : ℝ) = 12 + 12 + 0 by norm_num]
        refine add_lt_add (add_lt_add ?_ ?_) ?_
        . rw [← div_lt_iff₀' (by norm_num), Real.lt_sqrt (by norm_num)]
          nlinarith
        . rw [← div_lt_iff₀' (by norm_num), Real.lt_sqrt (by norm_num)]
          nlinarith
        . rw [← div_lt_iff₀' (by norm_num), Real.lt_sqrt (by norm_num)]
          nlinarith
      linarith
  . -- Finally, we verify that x = 5 is a solution.
    intro h
    simp [h]
    norm_num
    simp [show (16 : ℝ) = 4 ^ 2 by norm_num, show (9 : ℝ) = 3 ^ 2 by norm_num]
    ring