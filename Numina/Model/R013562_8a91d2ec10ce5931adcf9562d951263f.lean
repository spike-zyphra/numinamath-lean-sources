import Mathlib

theorem algebra_306574 {m : ℝ} (hm : m ≠ 0) (A B C D : ℝ)
    (hA : A^2 - 2 * m * A - 2 * m^2 = 0) (hB : B^2 - 2 * m * B - 2 * m^2 = 0)
    (hAB : A ≠ B) (hvertex : ∃ x y, x = (A + B) / 2 ∧ y = -m * x + m^2 ∧
    x^2 - 2 * m * x - 2 * m^2 = y) :
    A = -m ∧ B = m ∧ C = -m / 3 ∧ D = m / 3 := by
  rcases hvertex with ⟨x, y, hx_eq, hy_eq, h_eq⟩
  have h2 : A + B = 2 * m := by
    have h3 : A^2 - 2 * m * A - 2 * m^2 = 0 := hA
    have h4 : B^2 - 2 * m * B - 2 * m^2 = 0 := hB
    have h5 : A^2 - 2 * m * A - 2 * m^2 - (B^2 - 2 * m * B - 2 * m^2) = 0 := by
      linarith
    have h6 : (A - B) * (A + B - 2 * m) = 0 := by
      ring_nf at h5 ⊢
      linarith
    cases' (mul_eq_zero.1 h6) with h7 h8
    · -- Case A - B = 0
      exfalso
      apply hAB
      linarith
    · -- Case A + B - 2 * m = 0
      linarith
  have h1 : x = m := by
    have hx_eq' : x = (A + B) / 2 := hx_eq
    rw [show A + B = 2 * m by linarith [h2]] at hx_eq'
    linarith
  have h3 : y = 0 := by
    rw [h1] at hy_eq
    nlinarith
  -- From h_eq with x = m and y = 0: m^2 - 2 * m * m - 2 * m^2 = 0
  rw [h1] at h_eq
  -- nlinarith gives:
  have h4 : -3 * m^2 = 0 := by
    nlinarith [h3, h_eq]
  -- This gives a contradiction with hm.
  have h5 : m^2 = 0 := by
    linarith
  have h6 : m = 0 := by
    nlinarith
  contradiction