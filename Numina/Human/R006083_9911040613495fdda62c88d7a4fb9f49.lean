import Mathlib
/-Let $C$ be the unit circle. Four distinct, smaller congruent circles $C_{1}, C_{2}, C_{3}, C_{4}$ are internally tangent to $C$ such that $C_{i}$ is externally tangent to $C_{i-1}$ and $C_{i+1}$ for $i=$ $1, \ldots, 4$ where $C_{5}$ denotes $C_{1}$ and $C_{0}$ represents $C_{4}$. Compute the radius of $C_{1}$.-/

theorem geometry_611462 (R r' a: ℝ)
  -- Given the problem statement, four small circles are tangent to each other, 
  -- and their centers form a square. The diagonal of the square is twice the 
  -- sum of the radius of the small circle and the variable `a`.
  (hR: R = 1) -- The radius of the large circle is 1
  (ha: r' + a = R) -- The sum of the small circle radius and `a` equals the radius of the large circle
  (hr': 2 * Real.sqrt 2 * r' = 2 * a) -- The diagonal of the square is twice the side length (which is `sqrt(2) * r'`)
: r' = Real.sqrt 2 - 1 := by
  -- First, derive the relationship between `a` and `r'` from the given equation `hr'`
  have a_eq : a = Real.sqrt 2 * r' := by 
    symm at hr'
    linarith
  rw [a_eq, hR] at ha
  -- Simplify the equation to express `r'` in terms of constants
  have h₁ : (1 + Real.sqrt 2) * r' = 1 := by
    ring_nf at ha ⊢
    linarith [Real.sqrt_nonneg 2]
  -- Solve for `r'` by dividing both sides by `(1 + sqrt(2))`
  have h₂ : r' = 1 / (1 + Real.sqrt 2) := by
    apply Eq.symm
    field_simp [add_comm]
    linarith [Real.sqrt_nonneg 2]
  rw [h₂]
  field_simp [add_comm, sub_eq_add_neg, mul_comm]
  ring_nf
  norm_num