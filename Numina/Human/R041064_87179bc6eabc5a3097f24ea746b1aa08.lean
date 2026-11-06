import Mathlib

/- What is the smallest real number $x$ in the domain of the function $$g(x) = \sqrt{(x-3)^2-(x-8)^2}~?$$ -/
theorem algebra_18746 : IsLeast {x : ℝ | (x - 3) ^ 2 - (x - 8) ^ 2 ≥ 0} (11 / 2) := by
  constructor
  · -- if $x = 11 / 2$ then $(x - 3) ^ 2 - (x - 8) ^ 2 ≥ 0$
    norm_num
  · -- if $(x - 3) ^ 2 - (x - 8) ^ 2 ≥ 0$ then $x \geq 11 / 2$
    intro x hx
    simp only [ge_iff_le, sub_nonneg, Set.mem_setOf_eq] at hx
    linarith