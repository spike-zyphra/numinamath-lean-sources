import Mathlib

/- For example, $3 z \in \mathbf{C}, z^{7}=1(z \neq 1), z$ has an argument of $\alpha$, find the value of $\cos \alpha+\cos 2 \alpha+\cos 4 \alpha$. -/
theorem algebra_100766 (z : ℂ) (hz : z^7 = 1) (hz1 : z ≠ 1) (α : ℝ)
    (hα : α = Complex.arg z) :
    Real.cos α + Real.cos (2 * α) + Real.cos (4 * α) = -1 / 2 := by

  have z_nonzero : z ≠ 0 := by
    intro h
    simp [h] at hz
  have z_abs : Complex.abs z = 1 := by
    apply_fun Complex.abs at hz
    rw [Complex.abs_pow] at hz
    simp at hz
    rw [pow_eq_one_iff_of_nonneg (AbsoluteValue.nonneg' _ _) (by norm_num)] at hz
    exact hz

  -- First, note that cos α is the real part of z, cos 2α is the real part of z^2, and so on.
  have eval_pow (n : ℕ) : Complex.re (z^n) = Real.cos (n * α) := by
    rw [← Complex.abs_mul_exp_arg_mul_I z, ← hα]
    simp [z_abs]
    rw [← Complex.exp_nat_mul]
    rw [show ↑n * (↑α * Complex.I) = (n * α : ℝ) * Complex.I by push_cast; ring]
    rw [Complex.exp_ofReal_mul_I_re]

  -- This is useful because since z is a root of unity, the powers of z sum to zero.
  have eq1 : 1 + z^1 + z^2 + z^3 + z^4 + z^5 + z^6 = 0 := by
    rw [← mul_eq_zero_iff_right (show z - 1 ≠ 0 by simp [sub_eq_zero, hz1])]
    ring_nf
    simp [hz]

  -- We can rewrite the powers 3, 5, 6 in terms of 1, 2, 4.
  have flip_pow (n : ℕ) (h : n ≤ 7 := by norm_num) : Complex.re (z^n) = Complex.re (z^(7 - n)) := by
    have : z^n = (starRingEnd ℂ) (z^(7 - n)) := by
      rw [← Complex.inv_eq_conj (show Complex.abs (z^(7 - n)) = 1 by simp [Complex.abs_pow, z_abs])]
      rw [← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ z_nonzero)]
      rw [← pow_add]
      simp [h, hz]
    apply_fun Complex.re at this
    rw [Complex.conj_re] at this
    exact this

  -- Finally, we can put this all together to prove the result.
  apply_fun Complex.re at eq1
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at eq1
  rw [flip_pow 3, flip_pow 5, flip_pow 6] at eq1
  simp only [Nat.reduceSub, eval_pow] at eq1
  ring_nf at eq1
  rw [eq_div_iff (show (2 : ℝ) ≠ 0 by norm_num), ← add_eq_zero_iff_eq_neg]
  ring_nf
  exact eq1