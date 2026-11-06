import Mathlib

theorem algebra_325477 {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(z + 1) + Complex.I * (7 - z)‖ ≠ 5 * Real.sqrt 3 := by
  have h1 : ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf
  rw [h1] at hz
  have h2 : z.re ^ 2 + z.im ^ 2 = 1 := by
    calc
      z.re ^ 2 + z.im ^ 2 = (Real.sqrt (z.re ^ 2 + z.im ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = (1) ^ 2 := by rw [hz]
      _ = (1 : ℝ) := by norm_num
  have h3 : ‖(z + 1) + Complex.I * (7 - z)‖ = Real.sqrt ((z.re + z.im + 1) ^ 2 + (-z.re + z.im + 7) ^ 2) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im, pow_two]
    ring_nf
  rw [h3]
  by_contra h4
  have h5 : Real.sqrt ((z.re + z.im + 1) ^ 2 + (-z.re + z.im + 7) ^ 2) = 5 * Real.sqrt 3 := h4
  have h6 : (z.re + z.im + 1) ^ 2 + (-z.re + z.im + 7) ^ 2 = (5 * Real.sqrt 3) ^ 2 := by
    calc
      (z.re + z.im + 1) ^ 2 + (-z.re + z.im + 7) ^ 2 = (Real.sqrt ((z.re + z.im + 1) ^ 2 + (-z.re + z.im + 7) ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = (5 * Real.sqrt 3) ^ 2 := by rw [h5]
  have h7 : (5 * Real.sqrt 3) ^ 2 = 75 := by
    calc
      (5 * Real.sqrt 3) ^ 2 = 25 * (Real.sqrt 3) ^ 2 := by ring
      _ = 25 * 3 := by rw [Real.sq_sqrt]; positivity
      _ = (75 : ℝ) := by norm_num
  have h8 : (z.re + z.im + 1) ^ 2 + (-z.re + z.im + 7) ^ 2 = 75 := by
    linarith [h6, h7]
  have h9 : (z.re + z.im + 1) ^ 2 + (-z.re + z.im + 7) ^ 2 = 2 * (z.re ^ 2 + z.im ^ 2) - 12 * z.re + 16 * z.im + 50 := by
    nlinarith
  have h10 : (z.re + z.im + 1) ^ 2 + (-z.re + z.im + 7) ^ 2 = 52 - 12 * z.re + 16 * z.im := by
    rw [h9]
    have h14 : z.re ^ 2 + z.im ^ 2 = 1 := h2
    linarith [h14]
  have h11 : -12 * z.re + 16 * z.im = 23 := by
    nlinarith [h8, h10]
  nlinarith [sq_nonneg (z.re - (z.im * 4 / 3)), sq_nonneg (z.re * 4 - 3 * z.im *4), sq_nonneg (z.re * 3 -4 * z.im), sq_nonneg (z.re -4 /3 * (z.im) ), sq_nonneg (z.re * 4 -3 * z.im* 3 ), sq_nonneg (z.re - z.im), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)]