import Mathlib

theorem algebra_159421 {p : ℝ} (hp : p ≠ -2) :
    ((p^3 + 4 * p^2 + 10 * p + 12) / (p^3 - p^2 + 2 * p + 16)) *
    ((p^3 - 3 * p^2 + 8 * p) / (p^2 + 2 * p + 6)) = p := by

  have h1 : p^3 - p^2 + 2 * p + 16 ≠ 0 := by
    by_contra h
    have h2 : (p + 2) * (p^2 - 3 * p + 8) = 0 := by
      nlinarith [h]
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- h3: p + 2 = 0 → p = -2
      exfalso
      apply hp
      linarith
    · -- h4: p^2 - 3 * p + 8 = 0
      have h5 : p^2 - 3 * p + 8 > 0 := by
        nlinarith [sq_nonneg (p - 3 / 2)]
      nlinarith
  have h2 : p^2 + 2 * p + 6 ≠ 0 := by
    by_contra h
    have h3 : p^2 + 2 * p + 6 > 0 := by
      nlinarith [sq_nonneg (p + 1)]
    nlinarith

  have eq1 : p^3 + 4 * p^2 + 10 * p + 12 = (p + 2) * (p^2 + 2 * p + 6) := by
    ring

  have eq2 : p^3 - p^2 + 2 * p + 16 = (p + 2) * (p^2 - 3 * p + 8) := by
    ring

  have eq3 : p^3 - 3 * p^2 + 8 * p = p * (p^2 - 3 * p + 8) := by
    ring

  rw [eq1, eq2, eq3]

  have h3 : p + 2 ≠ 0 := by
    intro h
    apply hp
    linarith

  have h4 : p^2 - 3 * p + 8 ≠ 0 := by
    nlinarith [sq_nonneg (p - 3 / 2)]

  field_simp [(show (p^3 - p^2 + 2 * p + 16 : ℝ) ≠ 0 by assumption), (show (p^2 + 2 * p + 6 : ℝ) ≠ 0 by assumption), h3, h4]
  <;> ring