import Mathlib

theorem algebra_99524 (a : ℝ) (h : ∃ x : ℂ, x^2 - 2 * a * x + a^2 - 4 * a = 0 ∧ ‖x‖ = 3) :
    a = 1 ∨ a = 9 ∨ a = 2 - Real.sqrt 13 := by
  rcases h with ⟨x, hx_eq, hx_mod⟩
  have h_mod : ‖x‖ = Real.sqrt (x.re ^ 2 + x.im ^ 2) := by 
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf
  rw [h_mod] at hx_mod
  have h_eq : x.re ^ 2 + x.im ^ 2 = 9 := by
    calc
      x.re ^ 2 + x.im ^ 2 = (Real.sqrt (x.re ^ 2 + x.im ^ 2)) ^ 2 := by 
        rw [Real.sq_sqrt]
        positivity
      _ = 3 ^ 2 := by 
        rw [hx_mod]
      _ = 9 := by norm_num
  have eq1 := congr_arg Complex.re hx_eq
  have eq2 := congr_arg Complex.im hx_eq
  simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at eq1 eq2
  have h_eq2 : 2 * x.re * x.im - 2 * a * x.im = 0 := by 
    linarith
  have h_eq2_factored : 2 * x.im * (x.re - a) = 0 := by 
    linarith
  cases (mul_eq_zero.mp h_eq2_factored) with
  | inl h1 =>
    have h2 : x.im = 0 := by linarith [h1]
    have h3 : x.re ^ 2 = 9 := by 
      rw [h2] at h_eq
      nlinarith
    have h4 : x.re = 3 ∨ x.re = -3 := by
      have h5 : x.re ^ 2 - 9 = 0 := by linarith
      have h6 : (x.re - 3) * (x.re + 3) = 0 := by linarith [h5]
      cases (mul_eq_zero.mp h6) with
      | inl h7 => left; linarith
      | inr h8 => right; linarith
    rcases h4 with (h5 | h5)
    · -- x.re = 3
      have h6 : x.re = 3 := h5
      rw [h6, h2] at eq1
      have h10 : a^2 - 10 * a + 9 = 0 := by 
        nlinarith
      have h11 : (a - 1) * (a - 9) = 0 := by 
        nlinarith
      cases (mul_eq_zero.mp h11) with
      | inl h12 => 
        left
        linarith
      | inr h13 => 
        right
        left
        linarith
    · -- x.re = -3
      have h7 : x.re = -3 := h5
      rw [h7, h2] at eq1
      nlinarith [sq_nonneg (a + 1)]
  | inr h2 =>
    have h8 : x.re = a := by linarith [h2]
    have h9 : a ^ 2 + x.im ^ 2 = 9 := by 
      rw [h8] at h_eq
      nlinarith
    have h10 : x.im ^ 2 = -4 * a := by 
      rw [h8] at eq1
      nlinarith
    have h11 : a ^ 2 - 4 * a - 9 = 0 := by 
      nlinarith [h9, h10]
    have h12 : a ≤ 0 := by 
      nlinarith [h10, sq_nonneg x.im]
    have h13 : a = 2 - Real.sqrt 13 := by 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (13 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num), Real.sqrt_nonneg (13)]
    right
    right
    linarith