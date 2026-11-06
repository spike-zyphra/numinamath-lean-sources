import Mathlib
open Complex Real Finset

-- Add two theorems not included in Lean 4 version $4.15$.
lemma Complex.norm_mul_exp_arg_mul_I (x : ℂ) : ‖x‖ * exp (arg x * I) = x := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  · have : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    apply Complex.ext <;> field_simp [sin_arg, cos_arg hx, this, mul_comm ‖x‖]

lemma Complex.sq_norm_sub_sq_re (z : ℂ) : ‖z‖ ^ 2 - z.re ^ 2 = z.im ^ 2 := by
  have : ‖z‖ ^ 2 = normSq z := (normSq_eq_norm_sq z).symm
  rw [this, normSq_apply, ← sq, ← sq, add_sub_cancel_left]

/-During the weekends, Eli delivers milk in the complex plane. On Saturday, he begins at $z$ and delivers milk to houses located at $z^{3}, z^{5}, z^{7}, \ldots, z^{2013}$, in that order; on Sunday, he begins at 1 and delivers milk to houses located at $z^{2}, z^{4}, z^{6}, \ldots, z^{2012}$, in that order. Eli always walks directly (in a straight line) between two houses. If the distance he must travel from his starting point to the last house is $\sqrt{2012}$ on both days, find the real part of $z^{2}$.-/
theorem algebra_608962 :
    ∀ (z : ℂ), (∑ k ∈ range 1006, ‖z ^ (2 * k + 3) - z ^ (2 * k + 1)‖) = sqrt 2012 →
    (∑ k ∈ range 1006, ‖z ^ (2 * k + 2) - z ^ (2 * k)‖) = sqrt 2012 →
    (z ^ 2).re = 1005 / 1006 := by
  intro z h_sat h_sun
  -- Prove that $‖z‖ = 1$.
  have h_norm_z_eq_1 : ‖z‖ = 1 := by
    have h_eq : ‖z‖ * (∑ k ∈ range 1006, ‖z ^ (2 * k + 2) - z ^ (2 * k)‖) =
                ∑ k ∈ range 1006, ‖z ^ (2 * k + 3) - z ^ (2 * k + 1)‖ := by
      rw [mul_comm, sum_mul]
      apply sum_congr rfl
      intro k hk
      rw [← norm_mul]
      ring_nf
    rw [h_sat, h_sun] at h_eq
    have : √2012 ≠ 0 := by norm_num
    have : ‖z‖ = 1 := (mul_eq_right₀ this).mp h_eq
    exact this
  -- Prove that the Sunday path distance equals $1006 * ‖z ^ 2 - 1‖$.
  have h_sun_eq : ∑ k ∈ range 1006, ‖z ^ (2 * k + 2) - z ^ (2 * k)‖ = 1006 * ‖z ^ 2 - 1‖ := by
    have h₁: ∑ k ∈ range 1006, ‖z ^ (2 * k + 2) - z ^ (2 * k)‖ =
      ∑ k ∈ range 1006, ‖z ^ 2 - 1‖ * ‖z ^ (2 * k)‖ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← norm_mul]
      ring_nf
    have h₂: ∑ k ∈ range 1006, ‖z ^ 2 - 1‖ * ‖z ^ (2 * k)‖ = 1006 * ‖z ^ 2 - 1‖ := by
      rw [← Finset.mul_sum]
      have : ‖z ^ 2 - 1‖ * ∑ i ∈ range 1006, ‖z ^ (2 * i)‖ = ‖z ^ 2 - 1‖ * ∑ i ∈ range 1006, ‖z‖^ (2 * i) := by
        simp [Complex.abs_pow]
      rw [this, h_norm_z_eq_1]
      simp [one_pow]
      ring_nf
    rw [h₁, h₂]
  -- Derive from the Sunday distance that $‖z ^ 2 - 1‖ = sqrt(2012) / 1006$.
  have h_z2_minus_1 : ‖z ^ 2 - 1‖ = sqrt 2012 / 1006 := by
    rw [h_sun_eq] at h_sun
    have : 1006 ≠ 0 := by norm_num
    have : 1006 * ‖z ^ 2 - 1‖ = sqrt 2012 := h_sun
    nlinarith
  -- Prove that $z^2 = cos(2 * arg z) + i * sin(2 * arg z)$.
  have h_z2 : z ^ 2 = ↑(Real.cos (2 * Complex.arg z)) + I * ↑(Real.sin (2 * Complex.arg z)) := by
    have h_z_unit : z = Complex.exp (Complex.arg z * I) := by
      have := Complex.norm_mul_exp_arg_mul_I z
      rw [h_norm_z_eq_1, Complex.ofReal_one, one_mul] at this
      exact this.symm
    conv => left; rw [h_z_unit]
    have : Complex.exp (Complex.arg z * I) ^ 2 = Complex.exp (2 * Complex.arg z * I) := by
      rw [pow_two, ← Complex.exp_add]
      ring_nf
    rw [this, Complex.exp_mul_I]
    simp [Complex.cos]
    ring
  -- Prove that $|z^2 - 1| = sqrt(2 - 2 * cos(2 * arg z))$.
  have h_z2_minus_1_eq : ‖z ^ 2 - 1‖ = sqrt (2 - 2 * Real.cos (2 * arg z)) := by
    have : ‖z ^ 2 - 1‖ ^ 2 = 2 - 2 * Real.cos (2 * Complex.arg z) := by
      have h_norm_sq: ‖z ^ 2 - 1‖ ^ 2 = (z ^ 2 - 1).re ^ 2 + (z ^ 2 - 1).im ^ 2 := by
        nlinarith [Complex.sq_norm_sub_sq_re (z ^ 2 - 1)]
      have h_re_im : Complex.re (z ^ 2 - 1) = Real.cos (2 * Complex.arg z) - 1 ∧
                     Complex.im (z ^ 2 - 1) = Real.sin (2 * Complex.arg z) := by
        rw [h_z2]
        have h_re : Complex.re (↑(Real.cos (2 * Complex.arg z)) + I * ↑(Real.sin (2 * Complex.arg z)) + (-1)) =
                  Real.cos (2 * Complex.arg z) - 1 := by
          rw [Complex.add_re, Complex.add_re, Complex.ofReal_re,
          Complex.I_mul_re, Complex.ofReal_im, Complex.neg_re, Complex.one_re]
          ring
        have h_im : Complex.im (↑(Real.cos (2 * Complex.arg z)) + I * ↑(Real.sin (2 * Complex.arg z)) + (-1)) =
                    Real.sin (2 * Complex.arg z) := by
          rw [Complex.add_im, Complex.add_im, Complex.ofReal_im,
          Complex.I_mul_im, Complex.ofReal_re, Complex.neg_im, Complex.one_im]
          ring
        exact ⟨h_re, h_im⟩
      have h_expand : Complex.re (z ^ 2 - 1) ^ 2 + Complex.im (z ^ 2 - 1) ^ 2 =
                      (Real.cos (2 * Complex.arg z) - 1) ^ 2 + Real.sin (2 * Complex.arg z) ^ 2 := by
        rw [h_re_im.1, h_re_im.2]
      have h_trig : (Real.cos (2 * Complex.arg z) - 1) ^ 2 + Real.sin (2 * Complex.arg z) ^ 2 =
                    Real.cos (2 * Complex.arg z) ^ 2 - 2 * Real.cos (2 * Complex.arg z) + 1 +
                    Real.sin (2 * Complex.arg z) ^ 2 := by
        rw [pow_two]
        ring
      have h_cos_sin : Real.sin (2 * Complex.arg z) ^ 2 + Real.cos (2 * Complex.arg z) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
      have h_final : Real.cos (2 * Complex.arg z) ^ 2 - 2 * Real.cos (2 * Complex.arg z) + 1 +
                     Real.sin (2 * Complex.arg z) ^ 2 = 2 - 2 * Real.cos (2 * Complex.arg z) := by
        rw [add_comm, ← add_assoc, add_sub, h_cos_sin]
        ring
      rw [h_norm_sq, h_expand, h_trig, h_final]
    have h_pos1 : 0 ≤ ‖z ^ 2 - 1‖ := norm_nonneg (z ^ 2 - 1)
    have h_pos2 : 0 ≤ 2 - 2 * Real.cos (2 * Complex.arg z) := by nlinarith
    exact ((Real.sqrt_eq_iff_eq_sq h_pos2 h_pos1).mpr this.symm).symm
  -- Solve $2 - 2 cos(2θ)$ equals $2 / 1006$.
  have h_cos_2theta : Real.cos (2 * arg z) = 1005 / 1006 := by
    have h₁: ‖z ^ 2 - 1‖ ^ 2 = (sqrt 2012 / 1006) ^ 2 := by
      rw [h_z2_minus_1]
    have h₂: (sqrt 2012 / 1006) ^ 2 = 2012 / 1006 ^ 2 := by
      rw [div_pow, pow_two, pow_two]
      field_simp
    have h₃: (2012 : ℝ) / 1006 ^ 2 = 2 / 1006 := by norm_num
    rw [h₂,h₃] at h₁
    have h₄: ‖z ^ 2 - 1‖ ^ 2 = 2 - 2 * Real.cos (2 * arg z) := by
      rw [h_z2_minus_1_eq, Real.sq_sqrt (by nlinarith[Real.cos_le_one (2 * Complex.arg z)])]
    rw [h₄] at h₁
    have : Real.cos (2 * arg z) = -(2 / 1006 - 2) / 2 := by nlinarith
    simp [this]
    field_simp
    norm_num
  -- Compute the real part of $z^2$.
  have h_z2_re : (z ^ 2).re = Real.cos (2 * arg z) := by
    rw [h_z2]
    rw [Complex.add_re]
    rw [Complex.ofReal_re, Complex.I_mul_re, Complex.ofReal_im]
    ring
  rw [h_z2_re, h_cos_2theta]
