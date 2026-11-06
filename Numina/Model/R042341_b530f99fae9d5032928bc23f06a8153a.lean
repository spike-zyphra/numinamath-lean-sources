import Mathlib

theorem algebra_10755 {z : ℂ} (hz : z^2 = 4 * z - 19 + 8 * .I) (hzr : ∃ n : ℤ, Complex.abs z = n) :
    z = 3 + 4 * .I := by
  rcases hzr with ⟨n, hn⟩
  have h1 : z.re^2 - z.im^2 = 4 * z.re - 19 := by
    have h1 := congr_arg Complex.re hz
    simp [pow_two, Complex.add_re, Complex.ofReal_re, Complex.I_re, Complex.add_im, Complex.ofReal_im, Complex.I_im] at h1
    nlinarith

  have h2 : 2 * z.re * z.im = 4 * z.im + 8 := by
    have h2 := congr_arg Complex.im hz
    simp [pow_two, Complex.add_re, Complex.ofReal_re, Complex.I_re, Complex.add_im, Complex.ofReal_im, Complex.I_im] at h2
    nlinarith

  have h3 : Complex.abs z = Real.sqrt (z.re^2 + z.im^2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf

  rw [h3] at hn

  have h4 : z.re^2 + z.im^2 = (↑n : ℝ) ^ 2 := by
    calc
      z.re^2 + z.im^2 = (Real.sqrt (z.re^2 + z.im^2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = (↑n : ℝ) ^ 2 := by rw [hn]

  have h7 : (z.re - 3) * (z.re - 1) = 0 := by
    nlinarith [sq_nonneg (z.re - 3 : ℝ), sq_nonneg (z.im - 4 : ℝ), sq_nonneg (z.re - 1 : ℝ), sq_nonneg (z.im + 4 : ℝ)]

  have h8 : z.re = 3 ∨ z.re = 1 := by
    cases (mul_eq_zero.mp h7) with
    | inl h => 
      left
      linarith
    | inr h => 
      right
      linarith

  rcases h8 with h8 | h8
  · -- z.re = 3
    have h9 : z.im = 4 := by
      rw [show z.re = 3 by linarith [h8]] at h2
      nlinarith
    have h10 : z = 3 + 4 * Complex.I := by
      simp [Complex.ext_iff, h8, h9]
    exact h10
  · -- z.re = 1
    have h9 : z.im = -4 := by
      rw [show z.re = 1 by linarith [h8]] at h2
      nlinarith
    have h30 : (↑n : ℝ) ^ 2 = 17 := by
      rw [show z.re = 1 by linarith [h8], show z.im = -4 by linarith [h9]] at h4
      nlinarith
    have h31 : (n : ℝ) ^ 2 = (17 : ℝ) := by
      exact_mod_cast h30
    have h32 : n^2 = 17 := by
      exact_mod_cast h31
    -- Now derive a contradiction since 17 is not a perfect square
    have h33 : n ≤ 4 := by
      nlinarith [show n^2 ≥ 0 from sq_nonneg n]
    have h34 : n ≥ -4 := by
      nlinarith [show n^2 ≥ 0 from sq_nonneg n]
    interval_cases n <;> omega