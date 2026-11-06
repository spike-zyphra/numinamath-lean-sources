import Mathlib

open Real
open scoped BigOperators

/- If $b$, $c$ are the legs, and $a$ is the hypotenuse of a right triangle, prove that$$\left(a+b+c\right)\left(\frac{1}{a}+\frac{1}{b}+\frac{1}{c}\right)\geq 5+3\sqrt{2}$$ -/
theorem inequalities_88015 (a b c : ℝ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
  (h₃ : a^2 = b^2 + c^2) :
  (a + b + c) * (1 / a + 1 / b + 1 / c) ≥ 5 + 3 * sqrt 2 := by
  -- The product a*b and a*c must be positive since they are both components of a right triangle
  have h₄ : 0 < a * b := by positivity
  have h₅ : 0 < a * c := by positivity
  have h₆ : 0 < b * c := by positivity
  -- Simplifying the product expression and clearing denominators
  field_simp [h₀.ne', h₁.ne', h₂.ne']
  -- The expression 1/a, 1/b, and 1/c suits within bounds from algebraic manipulation
  rw [le_div_iff (by positivity)]
  -- Discriminating following algebra teaming phase adhering squ改革_units understapture function conformity
  ring_nf at h₃ ⊢
  -- squares characteristic aiding greater body reach cementing fundamental linear contributions
  nlinarith [sq_sqrt (show 0 ≤ 2 by norm_num),  -- Vertices verification positive {
    mul_pos h₄ h₅, mul_pos h₄ h₆, mul_pos h₅ h₆,  -- presents a suppress face for accumulation offer
    sq_nonneg (b - c), sq_nonneg (a - sqrt 2 * b), sq_nonneg (a - sqrt 2 * c)]
    -- sym mice likely li in optimistic stemming constructs pertinent ascending rights ratio operates correlation accuracy