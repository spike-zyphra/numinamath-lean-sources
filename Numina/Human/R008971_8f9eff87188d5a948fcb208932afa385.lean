import Mathlib

open Real

/-Let $x$ and $y$ be positive real numbers.  Find the minimum value of
\[\frac{\sqrt{(x^2 + y^2)(3x^2 + y^2)}}{xy}.\]-/
theorem algebra_16757 :
    IsLeast {m : ℝ | ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ m = sqrt ((x ^ 2 + y ^ 2) * (3 * x ^ 2 + y ^ 2)) / (x * y)} (1 + sqrt 3) := by
  simp [IsLeast, lowerBounds]
  -- goal devides into two parts
  refine ⟨?_, ?_⟩
  -- the inequality can be equal
  . use (1)
    simp
    use (sqrt (sqrt 3))
    simp
    field_simp
    -- handle the multiplcity of sqrt
    calc
      (1 + √3) * √√3 = √((1 + √3) ^ 2) * √√3 := by rw [@Real.sqrt_sq (1 + √3)]; positivity
      _ = √((1 + √3) * (1 + √3)) * √√3 := by ring_nf
      _ = √(1 + √3) * √(1 + √3) * √√3 := by rw[@Real.sqrt_mul (1 + √3)]; positivity
      _ = √(1 + √3) * √(√3 + √3 * √3) := by rw [mul_assoc, <-@Real.sqrt_mul (1 + √3)]; ring_nf; positivity
      _ = √(1 + √3) * √(3 + √3) := by rw[@Real.mul_self_sqrt 3]; ring_nf; positivity
  -- prove the inequality
  . intro m x hx y hy hm
    have ineq1 : 0 ≤ (√3 * x ^ 2 - y ^ 2) ^ 2 := by positivity
    --prove the Cauchy inequality
    have ineq2 : ((1 + √3) * (x * y)) ^ 2 ≤ (x ^ 2 + y ^ 2) * (3 * x ^ 2 + y ^ 2) := by
      ring_nf at ineq1 ⊢
      rw [@Real.sq_sqrt 3] at ineq1 ⊢
      linarith only [ineq1]
      repeat positivity
    
    -- use Cauchy's inequality to solve the m
    apply Real.sqrt_le_sqrt at ineq2
    rw [@Real.sqrt_mul (x ^ 2 + y ^ 2)] at hm ineq2
    field_simp at hm
    rw [<-hm] at ineq2
    rw [Real.sqrt_sq] at ineq2
    field_simp at ineq2
    exact ineq2
    repeat positivity
