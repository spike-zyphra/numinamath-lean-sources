import Mathlib

theorem algebra_16550 : IsGreatest {z : ℝ | ∃ x y : ℝ, x + y = 3 ∧
    z = x ^ 4 * y + x ^ 3 * y + x ^ 2 * y + x * y + x * y ^ 2 + x * y ^ 3 + x * y ^ 4} (400 / 11) := by
  constructor
  · -- Show that 400/11 is in the set.
    use (33 + Real.sqrt 209) / 22, (33 - Real.sqrt 209) / 22
    constructor
    · -- Show that x + y = 3
      nlinarith [Real.sqrt_nonneg 209, Real.sq_sqrt (show (0 : ℝ) ≤ (209 : ℝ) by norm_num)]
    · -- Show that the expression equals 400/11
      nlinarith [Real.sqrt_nonneg 209, Real.sq_sqrt (show (0 : ℝ) ≤ (209 : ℝ) by norm_num),
        sq_nonneg ((33 + Real.sqrt 209) / 22 - (33 - Real.sqrt 209) / 22)]
  · -- Show that 400/11 is the greatest element in the set
    intro z h
    rcases h with ⟨x, y, hxy, hz⟩
    have h1 : x ^ 4 * y + x ^ 3 * y + x ^ 2 * y + x * y + x * y ^ 2 + x * y ^ 3 + x * y ^ 4 = x * y * (40 - 11 * (x * y)) := by
      have h2 : y = 3 - x := by linarith
      rw [h2]
      nlinarith [sq_nonneg (x - (3 - x)), sq_nonneg (x * (3 - x) - 20 / 11)]
    rw [h1] at hz
    nlinarith [sq_nonneg ((x * y) - 20 / 11), sq_nonneg ((x - y) ^ 2), sq_nonneg ((x + y - 3) ^ 2), sq_nonneg ((x * y) ^ 2 - (20 / 11) ^ 2)]