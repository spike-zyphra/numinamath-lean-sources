import Mathlib

open Real

theorem inequalities_4356 (x y : ℝ) (h : x^2 + y^2 = 1) :
    3 / (1 + (x + y) ^ 2 / 4) ≤ 1 / (1 + x ^ 2) + 1 / (1 + y ^ 2) + 1 / (1 + x * y) ∧
    (3 / (1 + (x + y) ^ 2 / 4) = 1 / (1 + x ^ 2) + 1 / (1 + y ^ 2) + 1 / (1 + x * y) ↔ x = y) := by

  have h1 : 3 / (1 + (x + y) ^ 2 / 4) ≤ 1 / (1 + x ^ 2) + 1 / (1 + y ^ 2) + 1 / (1 + x * y) := by

    have h2 : 0 < (1 + x ^ 2 : ℝ) := by
      nlinarith [sq_nonneg x]
    have h3 : 0 < (1 + y ^ 2 : ℝ) := by
      nlinarith [sq_nonneg y]
    have h4 : 0 < (1 + (x + y) ^ 2 / 4 : ℝ) := by
      nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x^2 + y^2 - 1)]
    have h5 : 1 + x * y ≥ 1 / 2 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x^2 + y^2 - 1)]
    have h6 : 0 < (1 + x * y : ℝ) := by
      nlinarith [h5]
    have h7 : 1 / (1 + x^2) + 1 / (1 + y^2) = 3 / (2 + (x * y) ^ 2) := by
      have h1 : y^2 = 1 - x^2 := by linarith
      have h2 : 1 + x^2 ≠ 0 := by
        nlinarith [sq_nonneg x]
      have h3 : 1 + y^2 ≠ 0 := by
        nlinarith [sq_nonneg y, show y^2 = 1 - x^2 by linarith]
      field_simp [h2, h3]
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y), sq_nonneg (x^2 - y^2), h, sq_nonneg (x - y), sq_nonneg (x + y)]
    have h8 : 1 / (1 + x^2) + 1 / (1 + y^2) + 1 / (1 + x * y) = 3 / (2 + (x * y) ^ 2) + 1 / (1 + x * y) := by
      linarith [h7]
    rw [h8]
    have h13 : (3 / (1 + (x + y) ^ 2 / 4) ) ≤ (3 / (2 + (x * y) ^ 2) + 1 / (1 + x * y) : ℝ) := by
      have h15 : (1 + (x + y) ^ 2 / 4 : ℝ) > 0 := by
        nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x^2 + y^2 - 1)]
      have h16 : (2 + (x * y) ^ 2 : ℝ) > 0 := by
        nlinarith [sq_nonneg (x * y), sq_nonneg (x^2 + y^2 - 1), sq_nonneg (x - y), sq_nonneg (x + y)]
      have h17 : (1 + x * y : ℝ) > 0 := by
        nlinarith [h5]
      have h18 : (3 / (1 + (x + y) ^ 2 / 4) ) - (3 / (2 + (x * y) ^ 2) + 1 / (1 + x * y) : ℝ) ≤ 0 := by
        have h19 : (3 / (1 + (x + y) ^ 2 / 4) ) - (3 / (2 + (x * y) ^ 2) + 1 / (1 + x * y) : ℝ) =
            ( (3 * (2 + (x * y) ^ 2) * (1 + x * y) - (3 * (1 + (x + y) ^ 2 / 4) * (1 + x * y) + (1 + (x + y) ^ 2 / 4) * (2 + (x * y) ^ 2)) ) / ( (1 + (x + y) ^ 2 / 4) * (2 + (x * y) ^ 2) * (1 + x * y) ) ) := by
          field_simp
          <;> ring
        rw [h19] at *
        have h22 : ( (3 * (2 + (x * y) ^ 2) * (1 + x * y) - (3 * (1 + (x + y) ^ 2 / 4) * (1 + x * y) + (1 + (x + y) ^ 2 / 4) * (2 + (x * y) ^ 2)) ) ) ≤ 0 := by
          nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y - 1 / 2), sq_nonneg (x^2 + y^2 - 1), sq_nonneg (x + y - 0), sq_nonneg (x - y), sq_nonneg (x * y), sq_nonneg (x * y), sq_nonneg (x^2 - y^2)]
        have h20 : ( (1 + (x + y) ^ 2 / 4) * (2 + (x * y) ^ 2) * (1 + x * y) ) > 0 := by
          positivity
        apply div_nonpos_of_nonpos_of_nonneg h22 (by positivity)
      linarith
    linarith

  constructor
  · exact h1
  · constructor
    · -- Assume equality holds, prove x = y
      intro heq
      have h2 : 0 < (1 + x ^ 2 : ℝ) := by
        nlinarith [sq_nonneg x]
      have h3 : 0 < (1 + y ^ 2 : ℝ) := by
        nlinarith [sq_nonneg y]
      have h4 : 0 < (1 + x * y : ℝ) := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x^2 + y^2 - 1)]
      have h5 : (1 + (x + y) ^ 2 / 4 : ℝ) > 0 := by
        nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x^2 + y^2 - 1)]
      have h7 : 1 / (1 + x^2) + 1 / (1 + y^2) = 3 / (2 + (x * y) ^ 2) := by
        have h1 : y^2 = 1 - x^2 := by linarith
        have h2 : 1 + x^2 ≠ 0 := by
          nlinarith [sq_nonneg x]
        have h3 : 1 + y^2 ≠ 0 := by
          nlinarith [sq_nonneg y, show y^2 = 1 - x^2 by linarith]
        field_simp [h2, h3]
        nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y), sq_nonneg (x^2 - y^2), h, sq_nonneg (x - y), sq_nonneg (x + y)]
      have h8 : 1 / (1 + x^2) + 1 / (1 + y^2) + 1 / (1 + x * y) = 3 / (2 + (x * y) ^ 2) + 1 / (1 + x * y) := by
        linarith [h7]
      rw [h8] at heq
      have h14 : (x - y) ^ 2 = 0 := by
        field_simp at heq
        nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y - 1 / 2), sq_nonneg (x^2 - y^2), sq_nonneg (x^2 + y^2 - 1)]
      have h15 : x - y = 0 := by
        nlinarith
      linarith
    · -- Assume x = y, prove equality
      intro heq
      have h9 : x = y := by linarith [heq]
      have h10 : x^2 = 1 / 2 := by
        have h11 : x^2 + y^2 = 1 := h
        rw [show y = x by linarith [h9]] at h11
        nlinarith
      have h12 : (3 / (1 + (x + y) ^ 2 / 4) ) = 2 := by
        have h13 : x + y = 2 * x := by
          have h14 : y = x := by linarith [h9]
          nlinarith
        rw [h13]
        have h14 : (2 * x) ^ 2 = 4 * x^2 := by ring
        rw [h14]
        field_simp [h10]
        all_goals nlinarith
      have h13 : 1 / (1 + x ^ 2) + 1 / (1 + y ^ 2) + 1 / (1 + x * y) = 2 := by
        have h14 : y = x := by linarith [h9]
        rw [show y = x by linarith [h9]]
        have h15 : x ^ 2 = 1 / 2 := h10
        field_simp [h15, show 1 + x ^ 2 = 3 / 2 by nlinarith, show 1 + x * x = 3 / 2 by nlinarith]
        all_goals nlinarith [h10]
      linarith [h12, h13]