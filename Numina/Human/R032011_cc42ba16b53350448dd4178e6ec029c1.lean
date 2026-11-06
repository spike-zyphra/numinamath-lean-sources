import Mathlib
/-What is the sum of the lengths, in centimeters, of the two legs of a 30-60-90 right triangle, if the length of the hypotenuse is $2\sqrt{6}$ centimeters?-/
theorem algebra_21305 (a b c : ℝ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : a^2 + b^2 = c^2) (h₄ : c = 2 * Real.sqrt 6) (h₅ : a =  (Real.sin (Real.pi / 6)) * c) (h₆ : b =  Real.cos (Real.pi / 6) * c):
    a + b = Real.sqrt 6 + 3 * Real.sqrt 2 := by
    --We know that the ratio of the lengths of the sides of a 30-60-90 triangle is $1:\sqrt{3}:2$. We know that the length of the hypotenuse is $2\sqrt{6}$ and the ratio of the length shortest leg to that of the hypotenuse is $1:2$. Therefore, the length of the shorter leg is $\sqrt{6}$. Since the ratio of the shorter leg to the longer leg is $1:\sqrt{3}$, the length of the longer leg is $\sqrt{6} \cdot \sqrt{3} = 3\sqrt{2}$. The sum of the lengths of these two legs is $\boxed{\sqrt{6} + 3\sqrt{2}}$ centimeters.
    --Calculate the values of sin (π/6) and cos (π/6)
    norm_num [Real.sin_pi_div_six, Real.cos_pi_div_six] at h₅ h₆
    --Substitute c=2 * Real.sqrt 6 into the expressions for a and b
    rw [h₄] at h₅ h₆
    --Simplify the expression and verify that a+b=Real.sqrt 6+3 * Real.sqrt 2
    norm_num [h₅, h₆, mul_assoc]
    ring_nf
    rw [← Real.sqrt_mul, show (6 * 3 : ℝ) = 3 ^ 2 * 2 by ring_nf,Real.sqrt_mul,Real.sqrt_sq]
    <;> linarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 2]
