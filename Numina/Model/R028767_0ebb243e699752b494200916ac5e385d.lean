import Mathlib

theorem algebra_12664 {z1 z2 : ℂ} (h₁ : ‖z1‖ = 2 * ‖z2‖) (h₂ : ‖z1‖ = 2)
    (h₃ : ‖z1 + z2‖ = Real.sqrt 7) :
    ‖z1 - z2‖ = Real.sqrt 3 := by
  have h₄ : ‖z2‖ = 1 := by
    nlinarith
  have h11 : ‖z1‖ = Real.sqrt (z1.re ^ 2 + z1.im ^ 2 : ℝ) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf
  have h12 : ‖z2‖ = Real.sqrt (z2.re ^ 2 + z2.im ^ 2 : ℝ) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf
  have h13 : ‖z1 + z2‖ = Real.sqrt ((z1.re + z2.re : ℝ) ^ 2 + (z1.im + z2.im : ℝ) ^ 2) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq, Complex.add_re, Complex.add_im]
    <;> ring_nf
  have h14 : ‖z1 - z2‖ = Real.sqrt ((z1.re - z2.re : ℝ) ^ 2 + (z1.im - z2.im : ℝ) ^ 2) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq, Complex.sub_re, Complex.sub_im]
    <;> ring_nf
  rw [h13] at h₃
  have eq3 : (z1.re + z2.re : ℝ) ^ 2 + (z1.im + z2.im : ℝ) ^ 2 = (7 : ℝ) := by
    calc
      (z1.re + z2.re : ℝ) ^ 2 + (z1.im + z2.im : ℝ) ^ 2 = ((Real.sqrt ((z1.re + z2.re : ℝ) ^ 2 + (z1.im + z2.im : ℝ) ^ 2)) : ℝ) ^ 2 := by
        rw [Real.sq_sqrt]
        positivity
      _ = (Real.sqrt 7 : ℝ) ^ 2 := by
        rw [h₃]
      _ = (7 : ℝ) := by
        rw [Real.sq_sqrt]
        positivity

  have eq1 : z1.re ^ 2 + z1.im ^ 2 = (4 : ℝ) := by
    rw [h11] at h₂
    calc
      z1.re ^ 2 + z1.im ^ 2 = ((Real.sqrt (z1.re ^ 2 + z1.im ^ 2 : ℝ) ) : ℝ) ^ 2 := by
        rw [Real.sq_sqrt]
        positivity
      _ = (2 : ℝ) ^ 2 := by
        rw [h₂]
      _ = (4 : ℝ) := by
        norm_num

  have eq2 : z2.re ^ 2 + z2.im ^ 2 = (1 : ℝ) := by
    rw [h12] at h₄
    calc
      z2.re ^ 2 + z2.im ^ 2 = ((Real.sqrt (z2.re ^ 2 + z2.im ^ 2 : ℝ) ) : ℝ) ^ 2 := by
        rw [Real.sq_sqrt]
        positivity
      _ = (1 : ℝ) ^ 2 := by
        rw [h₄]
      _ = (1 : ℝ) := by
        norm_num

  have h15 : ‖z1 - z2‖ = Real.sqrt ((z1.re - z2.re : ℝ) ^ 2 + (z1.im - z2.im : ℝ) ^ 2) := h14
  have h16 : ((z1.re - z2.re : ℝ) ^ 2 + (z1.im - z2.im : ℝ) ^ 2) = (3 : ℝ) := by
    have h30 : (z1.re + z2.re : ℝ) ^ 2 + (z1.im + z2.im : ℝ) ^ 2 = (7 : ℝ) := eq3
    nlinarith
  rw [h15]
  rw [h16]