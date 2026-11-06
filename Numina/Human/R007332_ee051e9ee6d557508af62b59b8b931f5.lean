import Mathlib

/- 【Example 1.18】Prove: If

$$

\sin \alpha+\sin \beta+\sin \gamma=\cos \alpha+\cos \beta+\cos \gamma=0 \text {, }

$$


then

$$

\begin{array}{l}
\cos 3 \alpha+\cos 3 \beta+\cos 3 \gamma=3 \cos (\alpha+\beta+\gamma) \\
\sin 3 \alpha+\sin 3 \beta+\sin 3 \gamma=3 \sin (\alpha+\beta+\gamma)
\end{array}

$$
 -/
theorem algebra_274527 (α β γ : ℝ) (h₀ : Real.sin α + Real.sin β + Real.sin γ = 0)
    (h₁ : Real.cos α + Real.cos β + Real.cos γ = 0) :
    Real.cos (3 * α) + Real.cos (3 * β) + Real.cos (3 * γ) =
    3 * Real.cos (α + β + γ) ∧
    Real.sin (3 * α) + Real.sin (3 * β) + Real.sin (3 * γ) =
    3 * Real.sin (α + β + γ) := by
  -- We shift the identity to the complex numbers
  suffices (Real.cos (3 * α) + Real.cos (3 * β) + Real.cos (3 * γ))
      + (Real.sin (3 * α) + Real.sin (3 * β) + Real.sin (3 * γ)) * Complex.I
      = 3 * Real.cos (α + β + γ) + 3 * Real.sin (α + β + γ) * Complex.I by
    have ⟨hc, hs⟩ := Complex.ext_iff.mp this
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.add_im, Complex.ofReal_im, add_zero, Complex.I_im, mul_one, sub_self,
      Complex.re_ofNat, Complex.im_ofNat, sub_zero, Complex.mul_im, zero_mul, zero_add] at hc hs
    exact ⟨hc, hs⟩
  -- We complexify the hypothesis
  have complexify : (Real.cos α + Real.cos β + Real.cos γ) + (Real.sin α + Real.sin β + Real.sin γ) * Complex.I = 0 := by
    rw_mod_cast [h₀, h₁, zero_mul]
    exact AddZeroClass.zero_add 0
  -- It is α bit more convenient to have the hypothesis in this form
  have h : Complex.exp (α * Complex.I) + Complex.exp (β * Complex.I) = -Complex.exp (γ * Complex.I) := by
    rw [← sub_zero (Complex.exp (γ * Complex.I))]
    simp only [← Complex.cos_add_sin_I, ← complexify, Complex.ofReal_cos, Complex.ofReal_sin]
    ring

  -- We equate the cubes
  have cube : (Complex.exp (α * Complex.I) + Complex.exp (β * Complex.I))^3 = (-Complex.exp (γ * Complex.I))^3 := by
    congr

  -- We expand the cubes
  ring_nf at cube

  -- We collect the terms to build back the cos and sin of γ
  have : Complex.exp (α * Complex.I) * Complex.exp (Complex.I * β) ^ 2 * 3 +
          Complex.exp (α * Complex.I) ^ 2 * Complex.exp (Complex.I * β) * 3
        = Complex.exp (α * Complex.I) * Complex.exp ((Complex.I * β))
          * (Complex.exp ((α * Complex.I)) + Complex.exp (Complex.I * β)) * 3 := by ring

  -- We rewrite the terms in terms of cos and sin
  rw [this] at cube
  repeat rw [← Complex.exp_nat_mul, mul_comm Complex.I] at cube
  rw [h, ← Complex.exp_nat_mul] at cube
  ring_nf at cube
  repeat rw [← Complex.exp_add, mul_comm Complex.I, ← add_mul] at cube
  repeat rw [mul_comm _ 3] at cube
  repeat rw [← mul_assoc 3] at cube
  repeat rw [← Complex.cos_add_sin_I] at cube

  -- We get the desired identity on the complex numbers
  have : (Complex.cos (3 * α) + Complex.sin (3 * α) * Complex.I)
      + (Complex.cos (3 * β) + Complex.sin (3 * β) * Complex.I)
      + (Complex.cos (3 * γ) + Complex.sin (3 * γ) * Complex.I)
      = (3 * (Complex.cos (α + β + γ) + Complex.sin (α + β + γ) * Complex.I)) := by
        rw [← sub_neg_eq_add _ (Complex.cos (3 * γ) + Complex.sin (3 * γ) * Complex.I), ← cube]
        ring

  -- finally convert goal to complex
  repeat rw [Complex.ofReal_sin]
  repeat rw [Complex.ofReal_cos]
  push_cast
  linear_combination this