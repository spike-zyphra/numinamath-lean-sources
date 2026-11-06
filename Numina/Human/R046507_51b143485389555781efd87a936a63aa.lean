import Mathlib

/- Find all ordered triples $(x, y, z)$ of integers satisfying the
following system of equations:
$$
\begin{aligned}
x^{2}-y^{2} & =z \\
3 x y+(x-y) z & =z^{2}
\end{aligned}
$$ -/
theorem algebra_605576{x y z: ℤ}:
  (x^2-y^2=z ∧ 3*x*y+(x-y)*z=z^2) ↔
  ( (x=0 ∧ y=0 ∧ z=0) ∨ (x=1 ∧ y=0 ∧ z=1) ∨ (x=0 ∧ y=1 ∧ z=-1) ∨
    (x=1 ∧ y=2 ∧ z=-3) ∨ (x=2 ∧ y=1 ∧ z=3) ) := by
  constructor
  · -- the first direction. given two equations, decide x,y,z.
    rintro ⟨heq1, heq2⟩
    -- if z=0, then x=y=0 is the only solution.
    by_cases hzz: z = 0
    · simp [hzz] at heq1 heq2
      · rcases heq2 with hh | hh
        all_goals
          simp [hh] at heq1
          simp [hzz, hh, heq1]
    -- therefore we suppose z ≠ 0
    push_neg at hzz
    -- denote x+y = a, and x-y = b
    set a := x+y with a_def
    set b := x-y with b_def
    -- then first equation turns to be ab = z
    replace heq1: a*b = z := by
      rw [a_def, b_def, ← heq1]
      ring
    -- and x = (a+b)/2, y = (a-b)/2
    have x_of_ab: x = (a+b)/2 := by
      rw [a_def, b_def]
      simp [← mul_two]
    have y_of_ab: y = (a-b)/2 := by
      rw [a_def, b_def]
      simp [← mul_two]
    -- and second equation turns to be 3a^2-3b^2+4ab^2 = 4a^2b^2
    replace heq2: 3*a^2-3*b^2+4*a*b^2 = 4*(a*b)^2 := by
      rw [← heq1] at heq2
      rw [← heq2, x_of_ab, y_of_ab]
      have h1: 2 ∣ (a+b) := by
        rw [a_def, b_def]
        simp [← mul_two]
      have h2: 2 ∣ (a-b) := by
        rw [a_def, b_def]
        simp [← mul_two]
      rw [mul_assoc 3 _ _, mul_add 4 _ (b*(a*b)),
        ← mul_assoc 4 _ _, ← mul_assoc (4*3) _ _,
        ← Int.mul_ediv_assoc _ h1, ← Int.mul_ediv_assoc _ h2,
        mul_comm (4*3) _]
      ring_nf; rw [Int.mul_ediv_assoc x (by norm_num)]
      simp; ring
    -- re-arrange the second equation
    replace heq2: 3*a^2 = b^2 * (4*a^2-4*a+3) := by
      linarith [heq2]
    -- b cannot be 0, because we assume z ≠ 0, and ab = z
    have hb: b ≠ 0 := by
      rw [← heq1] at hzz
      exact right_ne_zero_of_mul hzz
    -- therefore b^2 ≥ 1
    replace hb: b^2 ≥ 1 := by
      exact (pow_two_pos_of_ne_zero hb)
    -- then 3a^2 ≥ 4a^2 - 4a + 3
    have hineq: 3*a^2 ≥ 4*a^2-4*a+3 := by
      rw [heq2]
      nlinarith [hb]
    -- that is to say, a^2-4a+3 ≤ 0, or (a-2)^2 ≤ 1
    replace hineq: (a-2)^2 ≤ 1 := by
      nlinarith [hineq]
    -- solve the inequality, a-2 = -1, 0, 1
    -- or a = 1, 2, 3
    have aeq: a = 1 ∨ a = 2 ∨ a = 3 := by
      rw [sq_le_one_iff_abs_le_one,
      Int.abs_le_one_iff] at hineq
      rcases hineq with hh | hh | hh
      all_goals simp [eq_add_of_sub_eq' hh]
    rcases aeq with aeq1 | aeq2 | aeq3
    · -- a=1, then b^2 = 1, b=1 or -1
      simp [aeq1] at heq2
      rcases heq2 with beq | beq
      all_goals
        -- a=b=1, we solve x=1,y=0, z=1
        -- and when a=1, b=-1, we solve x=0, y=1, z=-1
        simp [aeq1, beq] at x_of_ab y_of_ab heq1
        -- hence we find (1,0,1) and (0,1,-1)
        simp [x_of_ab, y_of_ab, ← heq1]
    · -- a=2, 12 = 11 b^2, no integer solution.
      simp [aeq2] at heq2
      omega
    · -- a=3, still b=1 or -1
      simp [aeq3] at heq2
      rcases heq2 with beq | beq
      all_goals
        -- a=3, b=1, we find (x,y,z) = (2,1,3)
        -- a=3, b=-1, we find (x,y,z) = (1,2,-3)
        simp [aeq3, beq] at x_of_ab y_of_ab heq1
        simp [x_of_ab, y_of_ab, ← heq1]
  · -- the other direction. verify these solutions satisfy the equations.
    rintro (h | h | h | h | h)
    all_goals simp [h]