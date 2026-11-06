import Mathlib

theorem algebra_1738 {x : ℝ} (hx : x ≠ 0) : (x + 1 / x) ^ 3 + (x - 1 / x) ^ 3 = 6 / x + 16 ↔ x = 2 := by
  constructor
  · -- Assume the equation holds, prove x = 2
    intro h_eq
    have eq1 : (x + 1 / x) ^ 3 + (x - 1 / x) ^ 3 = 2 * x ^ 3 + 6 / x := by
      field_simp
      ring
    rw [eq1] at h_eq
    have eq2 : 2 * x ^ 3 = 16 := by
      have eq3 : 2 * x ^ 3 + 6 / x = 6 / x + 16 := by linarith [h_eq]
      have h1 : x ≠ 0 := hx
      have eq4 : 2 * x ^ 3 = 16 := by
        have eq5 : 2 * x ^ 3 + 6 / x - (6 / x + 16) = 0 := by linarith
        have eq6 : 2 * x ^ 3 + 6 / x - (6 / x + 16) = 2 * x ^ 3 - 16 := by
          field_simp
          <;> ring
        rw [eq6] at eq5
        linarith
      exact eq4
    have eq3 : x ^ 3 = 8 := by
      linarith [eq2]
    have eq4 : x ^ 3 - 8 = 0 := by
      linarith [eq3]
    have eq5 : (x - 2) * (x ^ 2 + 2 * x + 4) = 0 := by
      ring_nf at eq4 ⊢
      linarith
    cases' (mul_eq_zero.mp eq5) with h1 h2
    · -- Case where x - 2 = 0
      linarith
    · -- Case where x^2 + 2x + 4 = 0
      have h3 : x ^ 2 + 2 * x + 4 > 0 := by
        nlinarith [sq_nonneg (x + 1)]
      nlinarith
  · -- Assume x = 2, prove the equation holds
    intro h_eq
    rw [h_eq]
    norm_num