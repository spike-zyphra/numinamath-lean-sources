import Mathlib

theorem algebra_4665 (x : ℝ) (hx : x > 0) :
    1 / (2 * x + 1) ^ ((1 : ℝ) / 4) -
    1 / (x + 2) ^ ((1 : ℝ) / 4) =
    (x - 1) / x ^ ((1 : ℝ) / 4) ↔ x = 1 := by

  constructor
  · -- Assume the equation holds, we need to prove x = 1
    intro h
    have hx1 : x ^ ((1 : ℝ) / 4) > 0 := by positivity
    by_contra h1
    replace h1 : x ≠ 1 := by exact h1
    have h2 : (1 : ℝ) / (2 * x + 1) ^ ((1 : ℝ) / 4) - 1 / (x + 2) ^ ((1 : ℝ) / 4) - (x - 1) / x ^ ((1 : ℝ) / 4) = 0 := by linarith
    have h3 : x = 1 := by
      have h4 : x > 0 := hx
      have h5 : (2 * x + 1) ^ ((1 : ℝ) / 4) > 0 := by positivity
      have h6 : (x + 2) ^ ((1 : ℝ) / 4) > 0 := by positivity
      have h7 : x ^ ((1 : ℝ) / 4) > 0 := by positivity
      have h8 : (2 * x + 1) ^ ((1 : ℝ) / 4) > (x + 2) ^ ((1 : ℝ) / 4) ↔ 2 * x + 1 > x + 2 := Real.rpow_lt_rpow_iff (by linarith) (by linarith) (by linarith [show (1 : ℝ) / 4 > 0 by norm_num])
      have h9 : (2 * x + 1) ^ ((1 : ℝ) / 4) < (x + 2) ^ ((1 : ℝ) / 4) ↔ 2 * x + 1 < x + 2 := Real.rpow_lt_rpow_iff (by linarith) (by linarith) (by linarith [show (1 : ℝ) / 4 > 0 by norm_num])
      have h10 : (x + 2) ^ ((1 : ℝ) / 4) > x ^ ((1 : ℝ) / 4) ↔ x + 2 > x := Real.rpow_lt_rpow_iff (by linarith) (by linarith) (by linarith [show (1 : ℝ) / 4 > 0 by norm_num])
      have h11 : (x + 2) ^ ((1 : ℝ) / 4) < x ^ ((1 : ℝ) / 4) ↔ x + 2 < x := Real.rpow_lt_rpow_iff (by linarith) (by linarith) (by linarith [show (1 : ℝ) / 4 > 0 by norm_num])
    
      by_cases h12 : x < 1
      · -- Case x < 1
        have h13 : (x + 2) ^ ((1 : ℝ) / 4) > x ^ ((1 : ℝ) / 4) := by
          rw [h10]
          linarith
        have h14 : (2 * x + 1) ^ ((1 : ℝ) / 4) < (x + 2) ^ ((1 : ℝ) / 4) := by
          rw [h9]
          linarith
        have h15 : 1 / (2 * x + 1) ^ ((1 : ℝ) / 4) - 1 / (x + 2) ^ ((1 : ℝ) / 4) > 0 := by
          have h16 : 1 / (2 * x + 1) ^ ((1 : ℝ) / 4) > 1 / (x + 2) ^ ((1 : ℝ) / 4) := by
            apply one_div_lt_one_div_of_lt
            all_goals linarith
          linarith
        have h17 : (x - 1) / x ^ ((1 : ℝ) / 4) < 0 := by
          apply div_neg_of_neg_of_pos
          · linarith
          · positivity
        linarith
    
      · -- Case x ≥ 1
        have h12 : x ≥ 1 := by by_contra!; linarith
        by_cases h13 : x = 1
        · -- Case x = 1
          exact h13
        · -- Case x > 1
          replace h13 : x > 1 := by
            by_contra!
            replace this : x = 1 := by linarith
            tauto
          have h14 : (2 * x + 1) ^ ((1 : ℝ) / 4) > (x + 2) ^ ((1 : ℝ) / 4) := by
            rw [h8]
            linarith
          have h15 : 1 / (2 * x + 1) ^ ((1 : ℝ) / 4) < 1 / (x + 2) ^ ((1 : ℝ) / 4) := by
            apply one_div_lt_one_div_of_lt
            all_goals linarith
          have h16 : 1 / (2 * x + 1) ^ ((1 : ℝ) / 4) - 1 / (x + 2) ^ ((1 : ℝ) / 4) < 0 := by linarith
          have h17 : (x - 1) / x ^ ((1 : ℝ) / 4) > 0 := by
            apply div_pos
            · linarith
            · positivity
          linarith
    contradiction

  · -- Now prove the reverse direction: x = 1 implies the equation holds
    intro h
    rw [h]
    norm_num