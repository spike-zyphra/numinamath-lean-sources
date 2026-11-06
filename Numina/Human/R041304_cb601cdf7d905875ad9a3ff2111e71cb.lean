import Mathlib

open Complex

/- A $120^\circ$ rotation around the origin in the clockwise direction is applied to $4 - \sqrt{3} + (-1 - 4 \sqrt{3})i.$  What is the resulting complex number? -/
theorem calculus_22849 (z : ℂ) (θ : Real.Angle) (hz : z = 4 - √3 + (-1 - 4 * √3) * I) (hθ : θ = (-2 * Real.pi / 3 : ℝ)) : z * θ.toCircle = -8 + 2 * I := by
  rw [hz, hθ, Real.Angle.coe_toCircle, Real.Angle.cos_coe, Real.Angle.sin_coe]
  have eq : Real.pi - 2 * Real.pi / 3 = Real.pi / 3 := by
    ring
  -- $\cos(\theta) = -1/2$
  have coseq : -Real.cos (-2 * Real.pi / 3 : ℝ) = 1 / 2 := by
    rw [neg_mul, neg_div, Real.cos_neg, ← Real.cos_pi_sub, eq, Real.cos_pi_div_three]
  apply congrArg (fun x ↦ -x) at coseq
  rw [neg_neg] at coseq
  -- $\sin(\theta) = -\sqrt{3}/2$
  have sineq : Real.sin (-2 * Real.pi / 3 : ℝ) = -√3 / 2 := by
    rw [neg_mul, neg_div, Real.sin_neg, ← Real.sin_pi_sub, eq, Real.sin_pi_div_three]
    ring
  -- compute $z * (\cos(\theta) + \sin(\theta)i)$
  rw [coseq, sineq]
  simp only [one_div, ofReal_neg, ofReal_inv, ofReal_ofNat, ofReal_div]
  ring_nf
  have sqrt3sq : (√3 : ℂ) ^ 2 = 3 := by
    have sqrteq : (√3 : ℂ) ^ 2 = (√3 ^ 2 : ℝ) := by
      exact Eq.symm (ofReal_pow (√3) 2)
    rw [sqrteq]
    simp only [Nat.ofNat_nonneg, Real.sq_sqrt, ofReal_ofNat]
  simp [sqrt3sq]
  ring