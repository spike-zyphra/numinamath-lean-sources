import Mathlib

open Real Set
open scoped Real

/- Let $\theta$ be an acute angle such that
\[\sin 5 \theta = \sin^5 \theta.\]Compute $\tan 2 \theta.$ -/
theorem calculus_23208 (θ : Real) (hθ : θ ∈ Ioo 0 (π / 2)) (h : sin (5 * θ) = sin θ ^ 5) :
    tan (2 * θ) = 2 * sqrt 2 := by
  rw [mem_Ioo] at hθ
  -- considering the imaginary parts of both sides of DeMoivre's formula, we have $\sin 5 \theta = 5 \cos^4 \theta \sin \theta - 10 \cos^2 \theta \sin^3 \theta + \sin^5 \theta$
  have demoivre := Complex.cos_add_sin_mul_I_pow 5 θ
  have eq1 : (5 : ℕ) * (θ : ℂ) = (5 * θ : ℝ) := by
    simp only [Nat.cast_ofNat, Complex.ofReal_mul, Complex.ofReal_ofNat]
  have eq2 : Complex.I ^ 3 = -Complex.I := by
    rw [← two_add_one_eq_three, pow_add, Complex.I_sq]
    ring
  have eq3 : Complex.I ^ 5 = Complex.I := by
    show Complex.I ^ (4 + 1) = Complex.I
    rw [pow_add, Complex.I_pow_four]
    ring
  rw [eq1] at demoivre
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin] at demoivre
  apply congrArg (fun x ↦ x.im) at demoivre
  ring_nf at demoivre
  simp only [Complex.I_pow_four, mul_one, Complex.I_sq,
    mul_neg, neg_mul, Complex.add_im, Complex.mul_im, Complex.mul_re, zero_mul, sub_zero, Complex.im_ofNat, mul_zero, add_zero, Complex.re_ofNat, zero_add, Complex.neg_im, Complex.I_re, Complex.I_im, zero_sub, Complex.ofReal_mul, Complex.ofReal_ofNat, one_mul, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im, neg_zero, eq2, eq3] at demoivre
  ring_nf at h
  apply sub_eq_zero_of_eq at demoivre
  rw [h] at demoivre
  -- so $5 \cos^2 \theta \sin \theta (\cos^2 \theta - 2 \sin^2 \theta) = 0$.
  have eq4 : -(cos θ ^ 2 * sin θ ^ 3 * 10) + cos θ ^ 4 * sin θ * 5 + sin θ ^ 5 - sin θ ^ 5 = 5 * cos θ ^ 2 * sin θ * (cos θ ^ 2 - 2 * sin θ ^ 2) := by
    ring
  -- since $\theta$ is acute, $\sin \theta$ and $\cos \theta$ are nonzero.
  have cosne : cos θ ≠ 0 := by
    have thetain : θ ∈ Ioo (-(π / 2)) (π / 2) := by
      constructor
      any_goals
      linarith
    apply Real.cos_pos_of_mem_Ioo at thetain
    linarith
  have sinne : sin θ ≠ 0 := by
    have thetain : θ ∈ Ioo 0 π := by
      constructor
      any_goals
      linarith
    apply Real.sin_pos_of_mem_Ioo at thetain
    linarith
  -- so $\cos^2 \theta - 2 \sin^2 \theta = 0$
  simp only [eq4, mul_eq_zero, OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, pow_eq_zero_iff, cosne, or_self, sinne, false_or] at demoivre
  apply eq_of_sub_eq_zero at demoivre
  -- so $\tan^2 \theta = 1 / 2$
  have tansqeq : tan θ ^ 2 = 1 / 2 := by
    rw [Real.tan_eq_sin_div_cos, div_pow, demoivre]
    field_simp
    ring
  -- since $\theta$ is acute, $\tan \theta = \sqrt{1 / 2}$
  have taneq : tan θ = sqrt (1 / 2) := by
    refine Eq.symm ((fun {x y} hx hy => (sqrt_eq_iff_eq_sq hx hy).mpr) ?_ ?_ (id (Eq.symm tansqeq)))
    norm_num
    apply Real.tan_nonneg_of_nonneg_of_le_pi_div_two
    any_goals
    linarith
  -- by the double-angle formula for tangent, $\tan 2 \theta = \frac{2 \tan \theta}{1 - \tan^2 \theta} = \frac{\sqrt{2}}{1 - \frac{1}{2}} = \boxed{2 \sqrt{2}}.$ 
  rw [Real.tan_two_mul, tansqeq, taneq]
  field_simp
  ring