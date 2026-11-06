import Mathlib

theorem algebra_12208 {z : ℂ} (hz : z ≠ 2017) (h : (2017 * z - 25) / (z - 2017) = 3 + 4 * .I) :
    Complex.abs z = 5 := by

  have h1 : z - 2017 ≠ 0 := by
    intro h2
    apply hz
    have h2' : z = 2017 := by
      have h22 : z - 2017 = 0 := by simpa using h2
      have : z = 2017 := by
        calc
          z = (z - 2017) + 2017 := by ring_nf
          _ = 0 + 2017 := by rw [h22]
          _ = 2017 := by ring_nf
      assumption
    assumption

  have eq1 : 2017 * z - 25 = (3 + 4 * Complex.I) * (z - 2017) := by
    have h2 : z - 2017 ≠ 0 := h1
    field_simp [h2] at h ⊢
    simpa using h

  have eq1' := eq1
  rw [Complex.ext_iff] at eq1
  simp at eq1 ⊢

  have eq2 : (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 = 25 := by
    nlinarith [sq_nonneg (z.re + 3), sq_nonneg (z.im + 4)]

  have h2 : Complex.abs z = Real.sqrt ((z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf

  rw [h2]

  have h3 : Real.sqrt ((z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2) = 5 := by
    rw [show (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 = (25 : ℝ) by linarith [eq2]]
    have h3 : Real.sqrt ((25 : ℝ)) = 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    exact h3

  exact h3