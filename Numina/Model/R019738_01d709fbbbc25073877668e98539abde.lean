import Mathlib

theorem algebra_302431 (a : ℝ) (h : ∃ z : ℂ, z^2 - 2 * a * z + a^2 - 4 * a = 0 ∧ ‖z‖ = 3) :
    a = 1 ∨ a = 9 ∨ a = 2 - Real.sqrt 13 := by
  rcases h with ⟨z, h_eq, h_mod⟩
  have h_mod' : ‖z‖ = Real.sqrt (z.re^2 + z.im^2) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring
  rw [h_mod'] at h_mod
  have h_mod_eq : Real.sqrt (z.re^2 + z.im^2) = 3 := h_mod
  have h_mod_sq : z.re^2 + z.im^2 = 9 := by 
    calc
      z.re^2 + z.im^2 = (Real.sqrt (z.re^2 + z.im^2))^2 := by rw [Real.sq_sqrt]; positivity
      _ = 3^2 := by rw [h_mod_eq]
      _ = 9 := by norm_num
  have eq1 := congr_arg Complex.re h_eq
  have eq2 := congr_arg Complex.im h_eq
  simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_add, add_mul] at eq1 eq2
  have eq4 : z.im * (2 * (z.re - a)) = 0 := by
    nlinarith
  cases (mul_eq_zero.mp eq4) with
  | inl h1 =>
    have h1' : z.im = 0 := h1
    rw [h1'] at eq1
    have eq5 : z.re^2 - 2 * a * z.re + a^2 - 4 * a = 0 := by nlinarith
    have eq6 : z.re^2 = 9 := by
      rw [h1'] at h_mod_sq
      nlinarith
    have h_re3 : z.re = 3 ∨ z.re = -3 := by
      have h7 : z.re^2 = 9 := eq6
      have : z.re = 3 ∨ z.re = -3 := by
        apply eq_or_eq_neg_of_sq_eq_sq
        norm_num
        linarith
      assumption
    cases h_re3 with
    | inl h_re3 =>
      rw [h_re3] at eq5
      have : a = 1 ∨ a = 9 := by
        have h8 : (1 - a) * (9 - a) = 0 := by
          nlinarith
        cases (mul_eq_zero.mp h8) with
        | inl h9 => 
          left
          linarith
        | inr h10 => 
          right
          linarith
      cases this with
      | inl h_a1 => 
        left
        linarith
      | inr h_a9 => 
        right
        left
        linarith
    | inr h_re3 =>
      rw [h_re3] at eq5
      nlinarith [sq_nonneg (a + 1)]
  | inr h2 =>
    have h2' : z.re = a := by
      nlinarith
    rw [h2'] at eq1
    have eq7 : a^2 - z.im^2 - 2 * a * a + a^2 - 4 * a = 0 := by
      nlinarith
    have eq8 : z.im^2 = -4 * a := by
      nlinarith
    have h_a_nonpos : a ≤ 0 := by
      nlinarith [sq_nonneg z.im]
    have eq9 : a^2 + z.im^2 = 9 := by
      rw [h2'] at h_mod_sq
      nlinarith
    have eq10 : a^2 - 4 * a - 9 = 0 := by
      nlinarith [eq8, eq9]
    have h_a_eq : a = 2 - Real.sqrt 13 := by
      have h11 : a^2 - 4 * a - 9 = 0 := eq10
      have h14 : a ≤ 0 := h_a_nonpos
      have h15 : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
      have : (a - (2 + Real.sqrt 13)) * (a - (2 - Real.sqrt 13)) = 0 := by
        nlinarith [Real.sqrt_nonneg 13]
      cases (mul_eq_zero.mp this) with
      | inl h16 =>
        nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show 0 ≤ (13 : ℝ) by norm_num)]
      | inr h17 =>
        linarith
    right
    right
    linarith [h_a_eq]