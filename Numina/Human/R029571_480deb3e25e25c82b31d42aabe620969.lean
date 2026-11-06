import Mathlib

/- Find $A$ and $B$ such that
\[\frac{4x}{x^2-8x+15} = \frac{A}{x-3} + \frac{B}{x-5}\]for all $x$ besides 3 and 5. Express your answer as an ordered pair in the form $(A, B).$ -/
theorem algebra_19287 {A B : ℝ} (h : ∀ x, x ≠ 3 → x ≠ 5 → 4 * x / (x ^ 2 - 8 * x + 15) = A / (x - 3) + B / (x - 5)) :
    A = -6 ∧ B = 10 := by
  -- notice that (x^2-8x+15) = (x-3)(x-5), so we can multiply both sides by (x-3)(x-5) to simplify
  have h1 (x:ℝ)(n3: x ≠ 3)(n5: x ≠ 5): 4*x = A*(x-5) + B*(x-3) := by
    have hh1 := h x n3 n5
    have hh2: x^2-8*x+15 = (x-3)*(x-5) := by ring
    have hh3: 4*x = 4*x / (x^2-8*x+15) * ((x-3)*(x-5)) := by
      rw [← hh2]
      have: (x^2-8*x+15) ≠ 0 := by
        rw [hh2]
        apply mul_ne_zero
        · exact sub_ne_zero_of_ne n3
        · apply sub_ne_zero_of_ne n5
      field_simp [this]
    rw [hh3, hh1]
    field_simp [sub_ne_zero_of_ne n3, sub_ne_zero_of_ne n5]
  -- 4x = A(x-5)+B(x-3) for all x (besides 3,5), we choose two values of x, then two equations can decide two unknown A and B.
  -- for example, we choose x=6.
  have eq1: A+3*B = 24 := by
    have := h1 6 (by norm_num) (by norm_num)
    norm_num at this
    simp [this, mul_comm]
  -- next, we choose x=4.
  have eq2: B-A = 16 := by
    have := h1 4 (by norm_num) (by norm_num)
    norm_num at this
    rw [this]; ring
  -- thus we can solve A and B
  have beq: B = 10 := by
    have: B = ((A+3*B)+(B-A))/4 := by ring
    rw [this, eq1, eq2]; ring
  have aeq: A = -6 := by
    rw [beq] at eq2
    linarith [eq2]
  exact ⟨aeq, beq⟩