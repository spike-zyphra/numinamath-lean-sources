import Mathlib
theorem number_theory_19060 {b : ℕ} (hb : b > 0) (hb2 : b > 4): (4: ℝ ) *(1 * b + 2) = (1* b^2 + 0 * b + 3) ↔ b = 5 := by
  constructor
  · -- Assume 4 * (1 * b + 2) = (1 * b^2 + 0 * b + 3), prove b = 5
    intro h
    have h1 : (b : ℝ) > (4 : ℝ) := by
      have h2 : (b : ℝ) > (4 : ℝ) := by
        exact_mod_cast hb2
      linarith
    have h2 : (4: ℝ ) * (1 * (b: ℝ) + 2) = (1 * ((b: ℝ) ^2) + 0 * (b: ℝ) + 3) := by
      linarith [h]
    have h3 : ((b : ℝ) - (5 : ℝ)) * ((b : ℝ) + (1 : ℝ)) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h3) with h4 h5
    · -- Case (b - 5) = 0
      have h6 : (b : ℝ) = (5 : ℝ) := by linarith
      have h7 : b = 5 := by
        exact_mod_cast h6
      exact h7
    · -- Case (b + 1) = 0
      have h8 : (b : ℝ) = (-1 : ℝ) := by linarith
      nlinarith [show (b : ℝ) > (0 : ℝ) from by exact_mod_cast hb]
  · -- Assume b = 5, prove the equation
    intro h
    rw [show (b : ℝ) = (5 : ℝ) by exact_mod_cast h]
    norm_num