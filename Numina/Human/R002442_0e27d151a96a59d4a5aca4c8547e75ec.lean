import Mathlib

/- The complex number z is equal to 9+bi, where b is a positive real number and i^2=−1.  Given that the imaginary parts 
of z^2 and z^3 are the same, what is b equal to? -/
theorem algebra_93429 {b : ℝ} (hb : b > 0) (z : ℂ) (hz : z = 9 + b * .I)
(h : (z ^ 2).im = (z ^ 3).im) : b = 15 := by {
  -- We start by recording some basic useful facts
  have hzim : z.im = b := by rw [hz]; simp
  have hzre: z.re = 9 := by rw [hz]; simp
  have hz2 : z^2 = z*z := by ring
  have hz3 : z^3 = z*z*z := by ring

  -- We rewrite the equation for the equality of (z^2).im and (z^3).im using the formulae for the real and imaginary part
  -- of the product of two complex numbers, resulting in an equation in b of degree 3.
  rw [hz2,hz3,Complex.mul_im,Complex.mul_im,Complex.mul_im,Complex.mul_re,hzim,hzre] at h
  ring_nf at h
  -- Now we factor the equation, which is easy because there is no constant part, so we can factor out b to make it
  -- a quadratic equation. This reveals the roots -15,0,15.
  have h' : (b - 15)*b*(b + 15) = 0 := by {
    calc
    (b-15)*b*(b+15) = b*18 + b^3 - b*243 := by ring
                  _ = 0 := by rw [h]; ring
  }
  rw [mul_eq_zero,mul_eq_zero] at h'
  -- We finally deduce the claim using the positivity of b.
  cases h' with 
    | inl hb1 => cases hb1 with
      | inl hb2 => linarith
      | inr hb3 => linarith
    | inr => linarith
}