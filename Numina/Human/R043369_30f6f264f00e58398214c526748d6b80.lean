import Mathlib

/- Find all values of $x$ that satisfy the equation $x = \!\sqrt{11-2x} + 4$. -/
theorem algebra_20501 (x : ℝ) (hx : x ≤ 11 / 2) :
    x = Real.sqrt (11 - 2 * x) + 4 ↔ x = 5 := by
  constructor
  · -- if the inequality holds then $x = 5$
    intro heq
    have heq2 := heq
    apply sub_eq_of_eq_add at heq
    apply congrArg (fun x ↦ x ^ 2) at heq
    rw [Real.sq_sqrt (by linarith)] at heq
    apply sub_eq_zero_of_eq at heq
    have eq : (x - 4) ^ 2 - (11 - 2 * x) = (x - 5) * (x - 1) := by
      ring
    rw [eq] at heq
    rw [mul_eq_zero] at heq
    rcases heq with heq | heq
    apply eq_of_sub_eq_zero at heq
    exact heq
    apply eq_of_sub_eq_zero at heq
    rw [heq] at heq2
    have sqrteq : √9 = 3 := by
      refine (Real.sqrt_eq_iff_mul_self_eq_of_pos ?_).mpr ?_
      any_goals
      norm_num
    norm_num [sqrteq] at heq2
  -- if $x = 5$ then the inequality holds
  intro xeq
  rw [xeq]
  norm_num