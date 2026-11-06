import Mathlib

theorem algebra_11565 {p : ℝ} (hp : p > 0) (h : ∃ x1 x2 : ℝ, x1 ≠ x2 ∧ x1^2 = p * x1 + 1 ∧ x2^2 = p * x2 + 1 ∧ |x2 - x1| = 5 * Real.sqrt 2 ∧
    Real.sqrt ((x2 - x1)^2 + (p * (x2 - x1))^2) = 4 / 3) :
    p = 3 := by
  rcases h with ⟨x1, x2, hx12, h1, h2, h3, h4⟩
  have h5 : (x2 - x1) ^ 2 = 50 := by
    have h51 : |x2 - x1| = 5 * Real.sqrt 2 := by
      simpa using h3
    have h511 : (x2 - x1) ^ 2 = (5 * Real.sqrt 2) ^ 2 := by
      calc
        (x2 - x1) ^ 2 = |x2 - x1| ^ 2 := by rw [sq_abs]
        _ = (5 * Real.sqrt 2) ^ 2 := by rw [h51]
    have h512 : (5 * Real.sqrt 2) ^ 2 = 50 := by
      calc
        (5 * Real.sqrt 2) ^ 2 = 25 * (Real.sqrt 2) ^ 2 := by ring
        _ = 25 * 2 := by
          rw [Real.sq_sqrt]
          all_goals norm_num
        _ = 50 := by
          norm_num
    rw [h511, h512]
  have h6 : Real.sqrt ((x2 - x1)^2 + (p * (x2 - x1))^2) = 4 / 3 := by
    simpa using h4
  have h61 : (x2 - x1)^2 + (p * (x2 - x1))^2 = (4 / 3) ^ 2 := by
    calc
      (x2 - x1)^2 + (p * (x2 - x1))^2 = (Real.sqrt ((x2 - x1) ^ 2 + (p * (x2 - x1)) ^ 2)) ^ 2 := by
        rw [Real.sq_sqrt]
        positivity
      _ = (4 / 3) ^ 2 := by
        rw [h6]
  nlinarith [Real.sqrt_nonneg ((x2 - x1) ^ 2 + (p * (x2 - x1)) ^ 2)]