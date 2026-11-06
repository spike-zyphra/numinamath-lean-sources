import Mathlib

open Real Set
open scoped Real

/- ## Zadatak B-3.4.

Riješite jednadžbu

$$

\frac{\sin \left(x-\frac{2015 \pi}{2}\right)-\cos ^{3} x}{\sin (2 x+2015 \pi)}=\frac{1}{2}

$$

 -/
theorem algebra_232857 (x : ℝ) :
    (sin (x - 2015 * π / 2) - cos x ^ 3) / sin (2 * x + 2015 * π) ≠ 1 / 2 := by 
  by_contra h
  --whenever k is 1 mod 4 we have that sin (x - (2 * k + 1) * π / 2) = - sin (x - π / 2), and this is the case for 2015.
  have k₁ : ∀ k : ℤ, Odd k → sin (x - (2 * k + 1) * π / 2) = - sin (x - π / 2) := by 
    intro k hk
    unfold Odd at hk
    obtain ⟨r, hr⟩ := hk
    rw[hr]
    push_cast
    rw[(by ring_nf : x - (2 * (2 * r + 1) + 1) * π / 2 = (x - π / 2 -  π) + (- r) * (2 * π))]
    norm_cast
    rw[sin_add_int_mul_two_pi (x - π / 2 -  π) (- r)]
    norm_num
  --for any k, sin (2 * x + (2 * k + 1) * π) = sin (2 * x + π).
  have k₂ : ∀ k : ℤ, sin (2 * x + (2 * k + 1) * π) = sin (2 * x + π) := by 
    intro k
    rw[add_mul, one_mul, add_comm (2 * k * π) π, ← add_assoc]
    rw[(by ring_nf : (2 * (k : ℝ)) * π = k * (2 * π)), sin_add_int_mul_two_pi (2 * x + π) k]
  
  specialize k₁ 1007 (by unfold Odd; use 503; ring_nf)
  specialize k₂ 1007
  norm_num at k₁ k₂
  --then rewrite the equalities in the equation.
  rw[k₁, k₂, sin_sub_pi_div_two] at h
  norm_num at h
  --rewrite using the formulas for sine of twice an angle and the identity sin x ^2 + cos x ^ 2 = 1.
  rw[(by ring_nf: cos x ^ 3 = cos x * cos x ^ 2)] at h
  nth_rw 1 [← mul_one (cos x)] at h
  rw[← mul_sub, sin_two_mul, ← sin_sq] at h
  --one has cos x and sin x ≠ 0 by existence conditions of the denominator
  have sin_ne_zero : sin x ≠ 0 := by 
    by_contra hk
    rw[hk] at h
    ring_nf at h
    linarith
  have cos_ne_zero : cos x ≠ 0 := by 
    by_contra hk
    rw[hk] at h
    ring_nf at h
    linarith
  --further algebraic simplification leads to sin x = -1
  rw[(by ring_nf: cos x * sin x ^ 2 / -(2 * sin x * cos x) = cos x / cos x * sin x / sin x * (- 1 / 2) * sin x)] at h
  rw[div_self (cos_ne_zero), one_mul, div_self (sin_ne_zero), one_mul] at h
  have hsin : sin x = - 1 := by linarith
  rw[← sin_pi_div_two, ← sin_neg, sin_eq_sin_iff] at hsin
  obtain ⟨k, hk₁|hk₂⟩ := hsin
  --this is true whenever x = - (π / 2) - 2 * k * π, but with the same angle cos x = 0 which is contradiction.
  · have hh1 : x = - (π / 2) - 2 * k * π := by linarith
    rw[hh1, cos_sub, cos_neg, sin_neg] at cos_ne_zero
    norm_num at cos_ne_zero
    rw[(by ring_nf : (2 * (k : ℝ)) * π = k * (2 * π))] at cos_ne_zero
    rw[← zero_add ((k : ℝ) * (2 * π)), sin_add_int_mul_two_pi] at cos_ne_zero
    rw[sin_zero] at cos_ne_zero
    push_neg at cos_ne_zero
    contradiction
  -- or x = π / 2 + (2 * k + 1) * π, but with the same angle cos x = 0 which is contradiction.
  · have hh2 : x = π / 2 + (2 * k + 1) * π := by linarith
    rw[hh2, cos_add] at cos_ne_zero
    norm_num at cos_ne_zero
    rw[(by ring_nf : (2 * (k : ℝ) + 1) * π = π + k * (2 * π))] at cos_ne_zero
    rw[sin_add, ← zero_add ((k : ℝ) * (2 * π)), sin_add_int_mul_two_pi, cos_add_int_mul_two_pi] at cos_ne_zero
    rw[sin_zero, sin_pi] at cos_ne_zero
    ring_nf at cos_ne_zero
    contradiction