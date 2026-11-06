import Mathlib

open Complex

theorem algebra_93142 (f : ℂ → ℂ) (hf : ∀ z, f z = (75 + 117 * I) * z + (96 + 144 * I) / z) (g : ℂ → Prop) (hg : ∀ z, g z ↔ ‖z‖ = 4) :
IsGreatest {t | ∃ z, g z ∧ (f z).re = t} 540 := by
  constructor
  · -- Show that 540 is in the set
    use 12 / 5 - (16 / 5) * I
    constructor
    · -- Show that g z is true, i.e., ‖z‖ = 4
      rw [hg]
      have h1 : ‖(12 / 5 - (16 / 5) * I)‖ = 4 := by
        simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq, Complex.re, Complex.im]
        ring_nf
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        all_goals norm_num
      exact_mod_cast h1
    · -- Show (f z).re = 540
      rw [hf]
      simp [pow_two, Complex.div_re, Complex.normSq, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.I_im]
      all_goals
      norm_num [Complex.normSq]
      <;> ring_nf
      <;> norm_num
      <;> field_simp [Complex.normSq]
      <;> linarith
  · -- Show that 540 is greatest
    intro t ht
    rcases ht with ⟨z, hz, ht⟩
    rw [hg] at hz
    have h1 : ‖z‖ = 4 := hz
    have h2 : (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 = 16 := by
      have h1' : ‖z‖ = Real.sqrt ((z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2) := by
        simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
        <;> ring_nf
        <;> simp [pow_two]
        <;> ring
      rw [h1'] at h1
      have h3 : Real.sqrt ((z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2) = 4 := h1
      have h4 : (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 = 16 := by
        calc
          (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 = (Real.sqrt ((z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2)) ^ 2 := by 
            rw [Real.sq_sqrt]
            positivity
          _ = 4 ^ 2 := by 
            rw [h3]
          _ = 16 := by 
            norm_num
      linarith
    have eq1 : (f z).re = 75 * z.re - 117 * z.im + (96 * z.re + 144 * z.im) / (z.re ^ 2 + z.im ^ 2) := by
      rw [hf]
      simp [pow_two, Complex.div_re, Complex.normSq, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.I_im]
      <;> ring_nf
      <;> field_simp [pow_two, Complex.normSq]
      <;> ring_nf
    rw [eq1] at ht
    have h7 : z.re ^ 2 + z.im ^ 2 = 16 := by
      linarith
    have h8 : 75 * z.re - 117 * z.im + (96 * z.re + 144 * z.im) / (z.re ^ 2 + z.im ^ 2) ≤ (540 : ℝ) := by 
      have h2 : z.re ^ 2 + z.im ^ 2 = 16 := h7
      have eq1 : (96 * z.re + 144 * z.im) / (z.re ^ 2 + z.im ^ 2) = (6 * z.re + 9 * z.im) := by
        rw [show (z.re ^ 2 + z.im ^ 2 : ℝ) = 16 by linarith]
        field_simp
        <;> linarith
        <;> ring_nf <;> norm_num
      rw [eq1]
      have h4 : z.re ^ 2 + z.im ^ 2 = 16 := h2
      nlinarith [sq_nonneg (z.re - 12 / 5), sq_nonneg (z.im + 16 / 5), sq_nonneg (z.re * 16 + z.im * 12), sq_nonneg (z.re * 9 - z.im * 12), sq_nonneg (z.re * 3 - 4 * z.im - 20), sq_nonneg (z.im + 16 / 5)]
    linarith [ht, h8]