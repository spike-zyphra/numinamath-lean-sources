import Mathlib

open Complex
/- 9) If the complex number $z$ satisfies $|z|=1$, and $z^{2}=a+b \mathrm{i}$, where $a, b$ are real numbers, then the maximum value of $a+b$ is $\qquad$ . -/
theorem algebra_273928 (z : ℂ) (hz : Complex.abs z = 1) :
    (z ^ 2).re + (z ^ 2).im ≤ Real.sqrt 2 ∧
    ∃ z : ℂ, Complex.abs z = 1 ∧ (z ^ 2).re + (z ^ 2).im = Real.sqrt 2 := by
    constructor
    rotate_left
    -- for proof of existence we take z^2 = √2/2 + i√2/2 -> z = √(2+√2)/2 + i√(2-√2)/2
    · use √(2+√2)/2 + I * √(2-√2)/2
      constructor
      · unfold Complex.abs normSq; simp
        calc √(2 + √2) / 2 * (√(2 + √2) / 2) + √(2 - √2) / 2 * (√(2 - √2) / 2)
        _ = √(2 + √2) / 2 * (√(2 + √2) / 2) + √(2 - √2) / 2 * (√(2 - √2) / 2) := by ring_nf
        _ = (√(2 + √2)^2 + √(2 - √2)^2) / 4 := by ring_nf
        _ = ((2 + √2) + (2 - √2)) / 4 := by rw [Real.sq_sqrt (by apply add_nonneg; simp; simp), Real.sq_sqrt (by simp; refine (Real.sqrt_le_left ?_).mpr ?_; simp; norm_num)]
        _ = 1 := by ring_nf
      · ring_nf; simp
        norm_cast; simp
        calc √(2 + √2) ^ 2 * 4⁻¹ + -(√(2 - √2) ^ 2 * 4⁻¹) + √(2 + √2) * √(2 - √2) * 2⁻¹
        _ = (2 + √2) * 4⁻¹ + -((2 - √2) * 4⁻¹) + √((2 + √2)*(2 - √2)) * 2⁻¹ := by rw [Real.sq_sqrt (by apply add_nonneg; simp; simp), Real.sq_sqrt (by simp; refine (Real.sqrt_le_left ?_).mpr ?_; simp; norm_num), ← Real.sqrt_mul (by apply add_nonneg; simp; simp)]
        _ = √2 * 2⁻¹ + √(2^2 - √2^2) / 2 := by ring_nf
        _ = √2 / 2 + √2 / 2 := by rw [Real.sq_sqrt (by norm_num)]; ring_nf
        _ = √2 := by ring_nf
    · -- we know that |z^2| = 1
      have h0:Complex.abs (z^2) = 1 := by
        simp; left; assumption
      -- now let z^2 = a + bi
      -- then we have a^2 + b^2 = 1
      let q:∃ a:ℝ, a = (z^2).re := by
        use (z^2).re
      obtain ⟨a, adef⟩ := q
      let q:∃ b:ℝ, b = (z^2).im := by
        use (z^2).im
      obtain ⟨b, bdef⟩ := q
      rw [abs_eq_sqrt_sq_add_sq] at h0
      rw [← adef, ← bdef] at h0 ⊢
      apply congr_arg (fun x => x^2) at h0
      rw [Real.sq_sqrt (by nlinarith)] at h0
      simp at h0
      -- it's sufficient to show that (a+b)^2 ≤ 2
      suffices (a+b)^2≤2 by exact Real.le_sqrt_of_sq_le this
      -- to do so we show that (a+b)^2 ≤ 2*(a^2+b^2)
      have h1: (a+b)^2≤ 2*(a^2+b^2) := by
        suffices 0 ≤ 2*(a^2+b^2) - (a+b)^2 by linarith
        conv_rhs =>
          calc _
          _ = (a-b)^2 := by ring_nf
        nlinarith
      -- which is just 2*1=2
      rw [h0] at h1
      simp at h1; assumption