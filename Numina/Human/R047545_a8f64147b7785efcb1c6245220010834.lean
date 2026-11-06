import Mathlib

/- ## Task B-4.3.

If $z_{1}, z_{2} \in \mathbb{C}$ are solutions to the equation $z+\frac{1}{z}=2 \sin \frac{\pi}{7}$, what is $z_{1}^{770}+z_{2}^{770}$? -/
theorem algebra_247269 {z1 z2 : ℂ} (hz1 : z1 ≠ 0) (hz2 : z2 ≠ 0)
    (h1 : z1 + 1 / z1 = 2 * Real.sin (Real.pi / 7)) (h2 : z2 + 1 / z2 = 2 * Real.sin (Real.pi / 7)) :
    z1 ^ 770 + z2 ^ 770 = -2 := by
  -- since there's not difference between z1 and z2 it suffices to show that if z solves h1 then z^770 = -1
  suffices ∀z:ℂ, z≠ 0 → z + 1/z = 2 * Real.sin (Real.pi / 7) → z^770 = -1 by
    have h1' := this z1 hz1 h1
    have h2' := this z2 hz2 h2
    rw [h1', h2']; norm_num
  -- now we can simplify the statement
  clear h1 h2 hz1 hz2 z1 z2
  intro z hzpos hz
  -- let's solve for z1 to see what the options are
  apply congr_arg (fun z' => z * z' -  z * (2 * Real.sin (Real.pi / 7))) at hz
  ring_nf at hz; rw [mul_inv_cancel₀ hzpos] at hz
  -- simple quadratic
  have sol := (quadratic_eq_zero_iff (a:=(1:ℂ)) (b:=-(Real.sin (Real.pi * (1 / 7))) * 2) (c:=1) (by norm_num) (s:=2*Complex.I * Real.cos (Real.pi/7))
  (by
    unfold discrim; norm_num; ring_nf; simp; rw [Complex.sin_sq]; ring_nf
  )
  z).mp
  ring_nf at sol; specialize sol hz
  -- let's analyze both cases
  cases' sol with sol sol
  -- in both cases we need to convert z into cos _ + i * sin _, then represent as root of unity and simplify
  <;> rw [sol]; clear sol hz
  · conv_lhs =>
      lhs
      calc _
      _ = Real.cos (Real.pi / 2 - Real.pi * (1 / 7)) + Complex.I * Real.sin (Real.pi / 2 - Real.pi * (1 / 7)) := by rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
      _ = Real.cos (5/14 * Real.pi) + Complex.I * Real.sin (5/14 * Real.pi) := by ring_nf
      _ = Complex.cos (5/14 * Real.pi) + Complex.I * Complex.sin (5/14 * Real.pi) := by simp
      _ = Complex.cos (5/14 * Real.pi) + Complex.sin (5/14 * Real.pi) * Complex.I := by ring_nf
    rw [Complex.cos_add_sin_mul_I_pow]; ring_nf
    conv_lhs =>
      calc _
      _ = Complex.cos (Real.pi + (137:ℕ) * (2 * Real.pi)) + Complex.sin (Real.pi + (137:ℕ) * (2 * Real.pi)) * Complex.I := by ring_nf
      _ = Complex.cos (Real.pi) + Complex.sin (Real.pi) * Complex.I := by rw [Complex.cos_add_nat_mul_two_pi, Complex.sin_add_nat_mul_two_pi]
      _ = -1 := by simp
  · conv_lhs =>
      lhs
      calc _
      _ = Real.cos (Real.pi / 2 - Real.pi * (1 / 7)) - Complex.I * Real.sin (Real.pi / 2 - Real.pi * (1 / 7)) := by rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
      _ = Real.cos (5/14 * Real.pi) - Complex.I * Real.sin (5/14 * Real.pi) := by ring_nf
      _ = Complex.cos (5/14 * Real.pi) - Complex.I * Complex.sin (5/14 * Real.pi) := by simp
      _ = Complex.cos (-(5/14 * Real.pi)) + Complex.sin (-(5/14 * Real.pi)) * Complex.I := by rw [← Complex.cos_neg, Complex.sin_neg]; ring_nf
    rw [Complex.cos_add_sin_mul_I_pow]; ring_nf
    conv_lhs =>
      calc _
      _ = Complex.cos (Real.pi + (-138:ℤ) * (2 * Real.pi)) + Complex.sin (Real.pi + (-138:ℤ) * (2 * Real.pi)) * Complex.I := by ring_nf
      _ = Complex.cos (Real.pi) + Complex.sin (Real.pi) * Complex.I := by rw [Complex.cos_add_int_mul_two_pi, Complex.sin_add_int_mul_two_pi]
      _ = -1 := by simp