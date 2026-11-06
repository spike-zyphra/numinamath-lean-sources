import Mathlib

/- Find all the solutions to
\[\sqrt{3x^2 - 8x + 1} + \sqrt{9x^2 - 24x - 8} = 3.\]Enter all the solutions, separated by commas. -/

theorem algebra_22643 : {x : ℝ | 0 ≤ (3 * x ^ 2 - 8 * x + 1) ∧ 0 ≤ (9 * x ^ 2 - 24 * x - 8) ∧ (√(3 * x ^ 2 - 8 * x + 1) + √(9 * x ^ 2 - 24 * x - 8) = 3)} = {3, -1 / 3} := by
  ext x
  simp only [sub_nonneg, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨le1, le2, heq⟩
    -- let $y = 3x ^2 - 8x + 1$
    let y := 3 * x ^ 2 - 8 * x + 1
    have yge : 0 ≤ 3 * y - 11 := by
      dsimp [y]
      linarith
    have eq1 : √y + √(3 * y - 11) = 3 := by
      dsimp [y]
      nth_rw 4 [← heq]
      ring_nf
    rw [add_comm] at eq1
    apply eq_sub_of_add_eq at eq1
    apply congrArg (fun x ↦ x ^ 2) at eq1
    rw [Real.sq_sqrt yge, sub_sq, Real.sq_sqrt le1] at eq1
    apply sub_eq_zero_of_eq at eq1
    apply congrArg (fun x ↦ -(x / 2)) at eq1
    ring_nf at eq1
    rw [add_sub] at eq1
    apply eq_of_sub_eq_zero at eq1
    -- $10 - y = 3\sqrt{y}$
    have eq2 : 10 - y = 3 * √y := by
      dsimp [y]
      ring_nf
      rw [← eq1]
      ring
    have eq3 := eq2
    apply congrArg (fun x ↦ x ^ 2) at eq3
    rw [mul_pow, Real.sq_sqrt le1] at eq3
    apply sub_eq_zero_of_eq at eq3
    ring_nf at eq3
    -- $y = 4, 25$
    have eq4 : (y - 4) * (y - 25) = 0 := by
      ring_nf
      exact eq3
    rw [mul_eq_zero] at eq4
    rcases eq4 with eq4 | eq4
    · -- when $y = 4$, solving this we get $x = 3, -1 / 3$
      ring_nf at eq4
      have eq5 : 3 * (x - 3) * (x - -1 / 3) = 0 := by
        ring_nf
        exact eq4
      rw [mul_eq_zero] at eq5
      rcases eq5 with eq5 | eq5
      left
      linarith
      right
      linarith
    · -- when $y = 25$, $10 - 6 = 3\sqrt{y}$ does not hold
      apply eq_of_sub_eq_zero at eq4
      have sq5eq : √25 = 5 := by
        refine (Real.sqrt_eq_iff_mul_self_eq_of_pos ?_).mpr ?_
        any_goals
        norm_num
      rw [eq4, sq5eq] at eq2
      norm_num at eq2
  · -- if $x = 3, -1 / 3$, then $x$ satisfies the equation
    intro xeq
    rcases xeq with xeq | xeq
    any_goals
    have sq2eq : √4 = 2 := by
      refine (Real.sqrt_eq_iff_mul_self_eq_of_pos ?_).mpr ?_
      any_goals
      norm_num
    norm_num [xeq, sq2eq]