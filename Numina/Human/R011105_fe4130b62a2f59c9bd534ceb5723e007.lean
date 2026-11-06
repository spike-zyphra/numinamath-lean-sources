import Mathlib

open Complex Polynomial

/-Let $a,$ $b,$ $c$ be complex numbers such that
\[a + b + c = ab + ac + bc = abc = 1.\]Enter the values $a,$ $b,$ $c,$ separated by commas, in any order.-/
theorem algebra_13014 {a b c : ℂ} (h₀ : a + b + c = 1) (h₁ : a * b + a * c + b * c = 1)
    (h₂ : a * b * c = 1) :
    ({a, b, c} : Multiset ℂ) = {1,I,-I} := by
  -- By Vieta's formulas, $a,$ $b,$ and $c$ are the roots of [x^3 - x^2 + x - 1 = 0.]
  have h1 : {a, b, c} = ((X - C a) * (X - C b) * (X - C c)).roots := by
    rw [roots_mul,roots_mul] 
    simp
    refine Monic.mul_left_ne_zero ?_ ?_
    exact monic_X_sub_C b
    exact X_sub_C_ne_zero a
    refine Monic.mul_left_ne_zero ?_ ?_
    exact monic_X_sub_C c
    refine Monic.mul_left_ne_zero ?_ ?_
    exact monic_X_sub_C b
    exact X_sub_C_ne_zero a
  have h2 : (X - C a) * (X - C b) * (X - C c) =  X ^ 3 - C (a + b + c) * X ^ 2 + C (a * b + a * c + b * c) * X - C (a * b * c) := by simp ;ring
  simp [h₀,h₁,h₂] at h2
  -- We can write this as $x^2 (x - 1) + (x - 1) = 0,$ or $(x - 1)(x^2 + 1) = 0.$ The roots are 1,i,-i.
  have h3 : X ^ 3 - X ^ 2 + X - 1 = (X - C 1) * (X - C I) * (X - C (-I)) := by
    ring_nf ;simp ;ring_nf
    have : C I ^ 2 = - 1 := by
      rw [← C_pow] ;simp
    rw [this] ;ring_nf
  rw [h2,h3] at h1
  have : (X - C 1) * (X - C I) ≠ 0 := by
    refine Monic.mul_left_ne_zero ?_ ?_
    exact monic_X_sub_C I
    exact X_sub_C_ne_zero 1
  rw [h1,roots_mul,roots_mul,roots_X_sub_C,roots_X_sub_C,roots_X_sub_C]
  simp
  exact this
  refine Monic.mul_left_ne_zero ?_ ?_
  exact monic_X_sub_C (-I)
  exact this
  
      