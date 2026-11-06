import Mathlib

open Real

/- Evaluate
\[\sum_{n = 0}^\infty \frac{\cos n \theta}{2^n},\]where $\cos \theta = \frac{1}{5}.$ -/
theorem calculus_23012 (θ : ℝ) (h : cos θ = 1 / 5) :
    ∑' n : ℕ, cos (n * θ) / 2 ^ n = 6 / 7 := by
  -- Consider the infinite geometric series \[1 + \frac{e^{i \theta}}{2} + \frac{e^{2i \theta}}{2^2} + \frac{e^{3i \theta}}{2^3} + \dotsb.\]
  have h1 : ∑'n : ℕ, (Complex.exp (θ * Complex.I) / 2) ^ n = (1 - Complex.exp (θ * Complex.I) / 2)⁻¹ := by
    apply tsum_geometric_of_norm_lt_one
    simp only [norm_div, Complex.norm_eq_abs, Complex.abs_exp_ofReal_mul_I, RCLike.norm_ofNat,
      one_div]
    norm_num
  have ne : 5 - 4 * Complex.cos ↑θ ≠ 0 := by
    by_contra contra
    apply congrArg (fun x ↦ x.re) at contra
    simp only [Complex.sub_re, Complex.re_ofNat, Complex.mul_re, Complex.im_ofNat, Complex.cos_ofReal_im, mul_zero, sub_zero, Complex.zero_re, Complex.cos_ofReal_re] at contra
    linarith
  -- $\frac{1}{1 - e^{i \theta}/2} = \frac{4 - 2 \cos \theta + 2i \sin \theta}{5 - 4 \cos \theta}$
  have h2 : (1 - Complex.exp (θ * Complex.I) / 2)⁻¹ = (4 - 2 * Complex.cos θ + 2 * Complex.I * Complex.sin θ) / (5 - 4 * Complex.cos θ) := by
    rw [← Complex.cos_add_sin_I]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [mul_div]
    apply div_eq_of_eq_mul
    exact ne
    -- simplify the equation
    ring_nf
    rw [Complex.I_sq]
    ring_nf
    rw [add_assoc, Complex.cos_sq_add_sin_sq]
    ring
  rw [h2] at h1
  -- Consider the real part ofg both sides
  apply congrArg (fun x ↦ x.re) at h1
  rw [Complex.re_tsum (by apply summable_geometric_of_norm_lt_one; simp; norm_num)] at h1
  -- ReReal part of right side is $6 / 7$
  have h3 : ((4 - 2 * Complex.cos ↑θ + 2 * Complex.I * Complex.sin ↑θ) / (5 - 4 * Complex.cos ↑θ)).re = (4 - 2 * cos θ) / (5 - 4 * cos θ) := by
    rw [div_eq_mul_inv]
    have mid : (5 - 4 * Complex.cos ↑θ)⁻¹ = (5 - 4 * cos θ)⁻¹ := by
      simp only [Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_ofNat, Complex.ofReal_mul, Complex.ofReal_cos]
    rw [mid, Complex.re_mul_ofReal]
    simp [Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im]
    ring
  rw [h] at h3
  -- Real part of left side is exactly the original series
  have h4 : ∀ n : ℕ, ((Complex.exp (↑θ * Complex.I) / 2) ^ n).re = cos (n * θ) / 2 ^ n := by
    intro n
    rw [div_pow, ← Complex.exp_nat_mul, ← mul_assoc, ← Complex.cos_add_sin_I, add_div, Complex.add_re, div_eq_mul_inv, div_eq_mul_inv]
    simp only [Complex.mul_re, Complex.inv_re, map_pow, Complex.normSq_ofNat, Complex.inv_im, Complex.I_re, mul_zero, Complex.I_im, mul_one, zero_sub, neg_mul, Complex.mul_im, add_zero]
    have mid : (2 ^ n : ℂ) = (2 ^ n : ℝ) := by
      simp only [Complex.ofReal_pow, Complex.ofReal_ofNat]
    have mid2 : (n * θ : ℂ) = (n * θ : ℝ) := by
      simp only [Complex.ofReal_mul, Complex.ofReal_natCast]
    simp only [mid, Complex.ofReal_re, Complex.ofReal_im, mid2, Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im]
    ring_nf
    rw [mul_assoc, ← mul_pow]
    ring
  -- So the sum is $6 / 7$
  rw [tsum_congr h4, h3] at h1
  rw [h1]
  norm_num