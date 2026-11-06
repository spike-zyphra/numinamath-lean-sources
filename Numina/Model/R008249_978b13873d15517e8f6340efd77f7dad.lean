import Mathlib

theorem algebra_19427 : {x : ℝ | 0 ≤ 6 - x - x ^ 2} = Set.Icc (-3) 2 := by 
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · -- Forward: if $0 \leq 6 - x - x^2$, then $x \in [-3, 2]$
    intro h
    constructor
    · -- Show that $x \geq -3$
      nlinarith [sq_nonneg (x + 3 / 2)]
    · -- Show that $x \leq 2$
      nlinarith [sq_nonneg (x + 3 / 2)]
  · -- Backward: if $x \in [-3, 2]$, then $0 \leq 6 - x - x^2$
    rintro ⟨h1, h2⟩
    nlinarith [sq_nonneg (x + 3 / 2)]