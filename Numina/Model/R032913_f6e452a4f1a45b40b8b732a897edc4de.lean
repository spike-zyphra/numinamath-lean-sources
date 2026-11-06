import Mathlib

theorem algebra_97454 {z1 z2 : ℂ} (hz1 : z1^2 - z1 = 5 - 5 * .I) (hz2 : z2^2 - z2 = 5 - 5 * .I)
    (hz12 : z1 ≠ z2) :
    (z1.re * z2.re) = -6 := by
  have eq1 : z1^2 - z1 - (5 - 5 * Complex.I) = 0 := by
    calc
      z1^2 - z1 - (5 - 5 * Complex.I) = (z1^2 - z1) - (5 - 5 * Complex.I) := by ring
      _ = (5 - 5 * Complex.I) - (5 - 5 * Complex.I) := by rw [hz1]
      _ = 0 := by ring
  have eq2 : z2^2 - z2 - (5 - 5 * Complex.I) = 0 := by 
    calc 
      z2^2 - z2 - (5 - 5 * Complex.I) = (z2^2 - z2) - (5 - 5 * Complex.I) := by ring
      _ = (5 - 5 * Complex.I) - (5 - 5 * Complex.I) := by rw [hz2]
      _ = 0 := by ring
  have eq3 : z1 = 3 - Complex.I ∨ z1 = -2 + Complex.I := by
    have h1 : z1^2 - z1 - (5 - 5 * Complex.I) = 0 := eq1
    have eq4 : z1.re^2 - z1.im^2 - z1.re - 5 = 0 := by
      have eq5 := congr_arg Complex.re h1
      simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, 
              Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im] at eq5 ⊢
      linarith
    have eq6 : 2 * z1.re * z1.im - z1.im + 5 = 0 := by
      have eq7 := congr_arg Complex.im h1
      simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, 
              Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im] at eq7 ⊢
      linarith
    have h2 : (z1.re - 3) * (z1.re + 2) = 0 := by
      nlinarith [sq_nonneg (z1.re - 3), sq_nonneg (z1.im + 1), sq_nonneg (z1.re + 2), sq_nonneg (z1.im - 1), 
        sq_pos_of_pos (show (0 : ℝ) < 2 by norm_num)]
    cases' (mul_eq_zero.mp h2) with h3 h4 
    · 
      left
      have hre : z1.re = 3 := by linarith
      have him : z1.im = -1 := by 
        nlinarith [hre]
      rw [Complex.ext_iff] at *
      simp [hre, him]
    · 
      right
      have hre : z1.re = -2 := by linarith
      have him : z1.im = 1 := by 
        nlinarith [hre]
      rw [Complex.ext_iff] at *
      simp [hre, him]
  have eq4 : z2 = 3 - Complex.I ∨ z2 = -2 + Complex.I := by
    have h1 : z2^2 - z2 - (5 - 5 * Complex.I) = 0 := eq2
    have eq4 : z2.re^2 - z2.im^2 - z2.re - 5 = 0 := by
      have eq5 := congr_arg Complex.re h1
      simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, 
              Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im] at eq5 ⊢
      linarith
    have eq6 : 2 * z2.re * z2.im - z2.im + 5 = 0 := by
      have eq7 := congr_arg Complex.im h1
      simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, 
              Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im] at eq7 ⊢
      linarith
    have h2 : (z2.re - 3) * (z2.re + 2) = 0 := by
      nlinarith [sq_nonneg (z2.re - 3), sq_nonneg (z2.im + 1), sq_nonneg (z2.re + 2), sq_nonneg (z2.im - 1), 
        sq_pos_of_pos (show (0 : ℝ) < 2 by norm_num)]
    cases' (mul_eq_zero.mp h2) with h3 h4 
    · 
      left
      have hre : z2.re = 3 := by linarith
      have him : z2.im = -1 := by
        nlinarith [hre]
      rw [Complex.ext_iff] at *
      simp [hre, him]
    · 
      right
      have hre : z2.re = -2 := by linarith
      have him : z2.im = 1 := by 
        nlinarith [hre]
      rw [Complex.ext_iff] at *
      simp [hre, him]
  cases eq3 with
  | inl h1 =>
    cases eq4 with
    | inl h2 =>
      exfalso
      exact hz12 (by
        rw [h1] at *
        rw [h2] at *
        all_goals
          simp_all
      )
    | inr h2 =>
      rw [h1, h2]
      norm_num
  | inr h1 =>
    cases eq4 with
    | inl h2 =>
      rw [h1, h2]
      norm_num
    | inr h2 =>
      exfalso
      exact hz12 (by
        rw [h1] at *
        rw [h2] at *
        all_goals
          simp_all
      )