import Mathlib

theorem algebra_161029 {x y : ℝ} (h1 : x^2 * y - x * y^2 - 5 * x + 5 * y + 3 = 0)
    (h2 : x^3 * y - x * y^3 - 5 * x^2 + 5 * y^2 + 15 = 0) :
    x = 4 ∧ y = 1 := by
  have eq1 : (x * y - 5) * (x - y) = -3 := by 
    nlinarith
  have eq2 : (x * y - 5) * (x - y) * (x + y) = -15 := by
    nlinarith
  have h3 : x + y = 5 := by
    have h4 : (x * y - 5) * (x - y) = -3 := eq1
    have h5 : (x * y - 5) * (x - y) * (x + y) = -15 := eq2
    rw [h4] at h5
    nlinarith
  have h4 : y = 5 - x := by linarith
  rw [h4] at eq1
  have h5 : x = 4 := by
    ring_nf at eq1
    have h6 : 2 * x ^ 3 - 15 * x ^ 2 + 35 * x - 28 = 0 := by nlinarith
    have h7 : (x - 4) * (2 * x ^ 2 - 7 * x + 7) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h7) with h8 h9
    · -- Case x -4=0, hence x=4
      linarith
    · -- Case 2x² -7x +7=0
      have h10 : 2 * x ^ 2 - 7 * x + 7 = 0 := by linarith
      nlinarith [sq_nonneg (x - 7 / 4)]
  have h6 : y = 1 := by
    rw [h5] at h4
    linarith
  exact ⟨h5, h6⟩