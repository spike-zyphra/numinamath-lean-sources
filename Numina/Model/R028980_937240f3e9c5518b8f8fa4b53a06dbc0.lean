import Mathlib

theorem inequalities_327196 (m n : ℕ) (h : m < Real.sqrt 11 * n) :
    11 * n^2 ≥ m^2 + 2 := by
  have h1 : (m : ℝ) < Real.sqrt 11 * (n : ℝ) := by
    exact_mod_cast h
  have h2 : (m : ℝ) ^ 2 < 11 * (n : ℝ) ^ 2 := by
    nlinarith [h1, Real.sqrt_nonneg 11, Real.sq_sqrt (show 0 ≤ (11 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 11) (show 0 ≤ (n : ℝ) by positivity)]
  have h4 : m^2 < 11 * n^2 := by
    have h5 : (m : ℝ) ^ 2 < (11 * (n : ℝ) ^ 2 : ℝ) := h2
    have h6 : (m^2 : ℝ) < (11 * n^2 : ℝ) := by
      nlinarith
    have h7 : m^2 < 11 * n^2 := by
      by_contra h8
      push_neg at h8
      have h8' : (m^2 : ℝ) ≥ (11 * n^2 : ℝ) := by
        exact_mod_cast h8
      linarith -- contradiction
    exact h7
  by_contra h8
  push_neg at h8
  have h8' : m^2 ≥ 11 * n^2 - 1 := by
    omega
  have h9 : m^2 ≤ 11 * n^2 - 1 := by
    omega
  have h10 : m^2 = 11 * n^2 - 1 := by
    omega
  have h11 : m^2 + 1 = 11 * n^2 := by
    omega
  have h12 : m^2 % 11 = 0 ∨ m^2 % 11 = 1 ∨ m^2 % 11 = 3 ∨ m^2 % 11 = 4 ∨ m^2 % 11 = 5 ∨ m^2 % 11 = 9 := by
    have h13 : m % 11 = 0 ∨ m % 11 = 1 ∨ m % 11 = 2 ∨ m % 11 = 3 ∨ m % 11 = 4 ∨ m % 11 = 5 ∨ m % 11 = 6 ∨ m % 11 = 7 ∨ m % 11 = 8 ∨ m % 11 = 9 ∨ m % 11 = 10 := by
      omega
    rcases h13 with (h | h | h | h | h | h | h | h | h | h | h) <;> simp [h, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
  have h13 : m^2 % 11 = 10 := by
    omega
  omega