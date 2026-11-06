import Mathlib

theorem algebra_261757 {x : ℝ} (hx : x > 0) (h : (x^2 / 3)^3 / 9 = x) : x = 3 := by
  have eq1 : (x^2 / 3) ^ 3 / 9 = x^6 / 243 := by
    ring_nf
    <;> nlinarith
  rw [eq1] at h
  have eq2 : x ^ 6 = 243 * x := by
    nlinarith
  have h1 : x * (x ^ 5 - 243) = 0 := by
    ring_nf at eq2 ⊢
    linarith
  cases' (mul_eq_zero.mp h1) with h2 h3
  · -- Case where x = 0, which contradicts x > 0
    linarith
  · -- Case where x^5 - 243 = 0
    have eq4 : x ^ 5 = 243 := by
      linarith
    have eq5 : x ^ 5 = (3 : ℝ) ^ 5 := by
      rw [eq4]
      norm_num
    have h4 : x = (3 : ℝ) := by
      have h5 : x ^ 5 = (3 : ℝ) ^ 5 := eq5
      have h6 : x > 0 := hx
      have h7 : (x : ℝ) ^ 5 - (3 : ℝ) ^ 5 = 0 := by
        nlinarith
      have h8 : (x - 3) * (x ^ 4 + 3 * x ^ 3 + 9 * x ^ 2 + 27 * x + 81) = 0 := by
        ring_nf at h7 ⊢
        nlinarith
      cases' (mul_eq_zero.mp h8) with h9 h10
      · -- Case where x - 3 = 0, so x = 3
        linarith
      · -- Case where the quartic equals zero, which is impossible
        nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x + 3 / 2), sq_nonneg (x - 3 / 2), sq_nonneg (x + 9 / 2)]
    linarith