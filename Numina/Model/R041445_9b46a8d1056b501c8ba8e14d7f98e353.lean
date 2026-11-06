import Mathlib

theorem number_theory_228406 {p q : ℝ} (hp : p > 0) (hq : q > 0) (hpq: p ≠ 2 * q)
    (h : Real.sqrt 7 = p / q) :
    Real.sqrt 7 = (7 * q - 2 * p) / (p - 2 * q) ∧ p - 2 * q > 0 ∧ p - 2 * q < q := by
  have h1 : p ^ 2 = 7 * q ^ 2 := by
    have h2 : Real.sqrt 7 = p / q := h
    have h3 : (Real.sqrt 7 : ℝ) ^ 2 = (p / q) ^ 2 := by
      rw [h2]
    have h4 : (Real.sqrt 7 : ℝ) ^ 2 = 7 := Real.sq_sqrt (by norm_num)
    rw [h4] at h3
    have h5 : (p / q) ^ 2 = p^2 / q^2 := by
      field_simp
    rw [h5] at h3
    have h6 : p ^ 2 = 7 * (q) ^ 2 := by
      field_simp at h3
      nlinarith
    linarith
  have h2 : p ^ 2 > 4 * q ^ 2 := by
    nlinarith [h1, sq_pos_of_pos hp, sq_pos_of_pos hq]
  have h4 : p - 2 * q > 0 := by
    nlinarith [sq_nonneg (p - 2 * q), sq_pos_of_pos hp, sq_pos_of_pos hq]
  have h5 : p - 2 * q < q := by
    nlinarith [h1, sq_pos_of_pos hp, sq_pos_of_pos hq]
  have h6 : Real.sqrt 7 = (7 * q - 2 * p) / (p - 2 * q) := by
    have h7 : Real.sqrt 7 = p / q := h
    have h7' : (p - 2 * q) ≠ 0 := by
      nlinarith
    have h8 : p * (p - 2 * q) = q * (7 * q - 2 * p) := by
      nlinarith [h1]
    field_simp [(show (p - 2 * q : ℝ) ≠ 0 by assumption), show (q : ℝ) ≠ 0 by linarith] at *
    <;> nlinarith [h7, Real.sqrt_nonneg 7, sq_nonneg (p - 2 * q)]
  constructor
  · exact h6
  constructor
  · exact h4
  · exact h5