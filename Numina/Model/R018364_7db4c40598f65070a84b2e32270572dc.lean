import Mathlib

theorem algebra_319867 (f : ℝ → ℝ) (hf : f = fun x => 3*x^3 + 2*Real.sqrt 2*x^2 - (17-9*Real.sqrt 2)*x - (6-5*Real.sqrt 2)) :
    f (Real.sqrt 2 / 3) = 0 ∧ f (Real.sqrt 2 - 1) = 0 ∧ f (1 - 2 * Real.sqrt 2) = 0 := by
  constructor
  · -- Show that f (sqrt 2 / 3) = 0
    rw [hf]
    have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ 2 by norm_num)
    have h2 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
      calc
        Real.sqrt 2 ^ 3 = (Real.sqrt 2) ^ 2 * Real.sqrt 2 := by ring
        _ = 2 * Real.sqrt 2 := by rw [h1]
    simp [h1, h2]
    ring_nf
    <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num)]
  constructor
  · -- Show that f (sqrt 2 - 1) = 0
    rw [hf]
    have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ 2 by norm_num)
    have h2 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
      calc
        Real.sqrt 2 ^ 3 = (Real.sqrt 2) ^ 2 * Real.sqrt 2 := by ring
        _ = 2 * Real.sqrt 2 := by rw [h1]
    simp [pow_two, pow_three, h1, h2]
    ring_nf
    <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num)]
  · -- Show that f (1 - 2 * Real.sqrt 2) = 0
    rw [hf]
    have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ 2 by norm_num)
    have h2 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
      calc
        Real.sqrt 2 ^ 3 = (Real.sqrt 2) ^ 2 * Real.sqrt 2 := by ring
        _ = 2 * Real.sqrt 2 := by rw [h1]
    simp [pow_two, pow_three, h1, h2]
    ring_nf
    <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num)]