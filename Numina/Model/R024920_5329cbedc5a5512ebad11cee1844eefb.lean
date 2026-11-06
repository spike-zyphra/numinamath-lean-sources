import Mathlib

theorem algebra_316064 {a : ℤ} (ha : 0 ≤ 5 * a ^ 2 - 26 * a - 8) :
    ∃ x1 x2 : ℤ, x1 ^ 2 - Real.sqrt (5 * a ^ 2 - 26 * a - 8) * x1 -
      (a ^ 2 - 4 * a + 9) = 0 ∧ x2 ^ 2 - Real.sqrt (5 * a ^ 2 - 26 * a - 8) * x2 -
      (a ^ 2 - 4 * a + 9) = 0 ↔ a = 6 := by
  use 7, -3
  constructor
  · -- Forward direction
    intro h
    rcases h with ⟨h1, h2⟩
    have eq3 : (7 : ℝ) ^ 2 - Real.sqrt (5 * a ^ 2 - 26 * a - 8) * (7 : ℝ) - (a ^ 2 - 4 * a + 9 : ℝ) = 0 := by
      simpa using h1
    have eq4 : (-3 : ℝ) ^ 2 - Real.sqrt (5 * a ^ 2 - 26 * a - 8) * (-3 : ℝ) - (a ^ 2 - 4 * a + 9 : ℝ) = 0 := by
      simpa using h2
    have h3 : Real.sqrt (5 * a ^ 2 - 26 * a - 8) = 4 := by
      nlinarith
    have h4 : (Real.sqrt (5 * a ^ 2 - 26 * a - 8) ^ 2 : ℝ) = (16 : ℝ) := by
      rw [h3]
      norm_num
    have h5 : (5 * a ^ 2 - 26 * a - 8 : ℝ) = (16 : ℝ) := by
      have h6' : Real.sqrt (5 * a ^ 2 - 26 * a - 8) ^ 2 = (5 * (a : ℝ) ^ 2 - 26 * (a : ℝ) - 8 : ℝ) := by
        have hx : 0 ≤ (5 * (a : ℝ) ^ 2 - 26 * (a : ℝ) - 8 : ℝ) := by
          exact_mod_cast ha
        rw [Real.sq_sqrt hx]
      linarith
    have h7 : (5 * a ^ 2 - 26 * a - 8 : ℤ) = (16 : ℤ) := by
      exact_mod_cast h5
    have h8 : (5 * a ^ 2 - 26 * a - 24 : ℤ) = (0 : ℤ) := by
      linarith
    have eq5 : (5 * a + 4 : ℤ) * (a - 6 : ℤ) = (0 : ℤ) := by
      nlinarith
    cases' (mul_eq_zero.mp eq5) with h9 h10
    · -- Case where a = -4/5
      omega
    · -- Case where a = 6
      omega
  · -- Reverse direction
    intro h
    rw [h]
    constructor
    · -- First equation
      have h5 : Real.sqrt (5 * (6 : ℤ) ^ 2 - 26 * (6 : ℤ) - 8) = (4 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h5]
      norm_num
    · -- Second equation
      have h5 : Real.sqrt (5 * (6 : ℤ) ^ 2 - 26 * (6 : ℤ) - 8) = (4 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h5]
      norm_num