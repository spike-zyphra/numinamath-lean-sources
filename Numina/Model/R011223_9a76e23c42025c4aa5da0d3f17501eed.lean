import Mathlib

theorem algebra_4665 (x : ℝ) (hx : x > 0) :
    1 / (2 * x + 1) ^ ((1 : ℝ) / 4) -
    1 / (x + 2) ^ ((1 : ℝ) / 4) =
    (x - 1) / x ^ ((1 : ℝ) / 4) ↔ x = 1 := by
  constructor
  · -- Assume the equation holds. Prove x = 1.
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
        have h16 : (x - 1) / x ^ ((1 : ℝ) / 4) < 0 := by
          have hx10 : x ^ ((1 : ℝ) / 4) > 0 := by positivity
          have hx11 : x - 1 < 0 := by linarith
          apply div_neg_of_neg_of_pos hx11 hx10
        have h17 : (1 : ℝ) / (2 * x + 1) ^ ((1 : ℝ) / 4) - 1 / (x + 2) ^ ((1 : ℝ) / 4) - (x - 1) / x ^ ((1 : ℝ) / 4) > 0 := by linarith
        linarith
      · -- Case x ≥ 1, so x > 1 since x ≠ 1
        have h12a : x > 1 := by
          by_contra h
          push_neg at h
          have h17 : x = 1 := by linarith
          contradiction
        have h13 : (2 * x + 1) ^ ((1 : ℝ) / 4) > (x + 2) ^ ((1 : ℝ) / 4) := by
          rw [h8]
          nlinarith
        have h14 : (x + 2) ^ ((1 : ℝ) / 4) < (2 * x + 1) ^ ((1 : ℝ) / 4) := by
          linarith
        have h15 : 1 / (2 * x + 1) ^ ((1 : ℝ) / 4) - 1 / (x + 2) ^ ((1 : ℝ) / 4) < 0 := by
          have h16 : 1 / (2 * x + 1) ^ ((1 : ℝ) / 4) < 1 / (x + 2) ^ ((1 : ℝ) / 4) := by
            apply one_div_lt_one_div_of_lt
            all_goals linarith
          linarith
        have h16 : (x - 1) / x ^ ((1 : ℝ) / 4) > 0 := by
          apply div_pos
          all_goals linarith
        have h17 : (1 : ℝ) / (2 * x + 1) ^ ((1 : ℝ) / 4) - 1 / (x + 2) ^ ((1 : ℝ) / 4) - (x - 1) / x ^ ((1 : ℝ) / 4) < 0 := by linarith
        linarith
    contradiction
  · -- Assume x = 1. Prove the equation.
    intro h
    rw [h]
    have h1 : (2 * (1 : ℝ) + 1) ^ ((1 : ℝ) / 4) = (3 : ℝ) ^ ((1 : ℝ) / 4) := by norm_num
    have h2 : (1 + 2 : ℝ) ^ ((1 : ℝ) / 4) = (3 : ℝ) ^ ((1 : ℝ) / 4) := by norm_num
    have h3 : ((1 : ℝ) : ℝ) ^ ((1 : ℝ) / 4) = 1 := by
      have h4 : (1 : ℝ) ^ ((1 : ℝ) / 4) = 1 := by
        rw [show (1 : ℝ) / 4 = (1 : ℝ) / 4 by rfl]
        simp
      linarith
    rw [h1, h2, h3]
    all_goals norm_num