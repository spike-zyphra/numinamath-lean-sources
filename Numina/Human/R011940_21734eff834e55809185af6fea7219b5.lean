import Mathlib

/-let f(x) = |x + 1| + |x| - |x - 2|. Then the number of different solutions
of f(f(x)) + 1 = 0 is -/

def f: ℝ → ℝ := fun x => |x + 1| + |x| - |x - 2|

theorem algebra_164686: {x: ℝ | f (f x) + 1 = 0}.encard = 3 := by

  -- we directly compute the solutions
  have h_eq: {x: ℝ | f (f x) + 1 = 0} = {-1, -3, 1 / 3} := by
    ext x
    constructor
    -- the left to right direction
    .
      intro h
      simp at h
      simp
      set a:= f x

      -- we show that a = -2 or 0
      have o: a = -2 ∨ a = 0 := by
        clear_value a
        simp [f] at h
        by_cases l1: a < -1

        -- case 1: a < -1
        .
          rw [show |a + 1| = -(a + 1) by apply abs_of_neg; linarith] at h
          rw [show |a| = -a by apply abs_of_neg; linarith] at h
          rw [show |a - 2| = -(a - 2) by apply abs_of_neg; linarith] at h
          left
          nlinarith
        .
          simp at l1
          by_cases l2: a < 0

          -- case 2: -1 ≤ a < 0
          .
            rw [show |a + 1| = a + 1 by apply abs_of_nonneg; linarith] at h
            rw [show |a| = -a by apply abs_of_neg; linarith] at h
            rw [show |a - 2| = -(a - 2) by apply abs_of_neg; linarith] at h
            nlinarith
          .
            simp at l2
            by_cases l3: a < 2

            -- case 3: 0 ≤ a < 2
            .
              rw [show |a + 1| = a + 1 by apply abs_of_nonneg; linarith] at h
              rw [show |a| = a by apply abs_of_nonneg; linarith] at h
              rw [show |a - 2| = -(a - 2) by apply abs_of_neg; linarith] at h
              right
              nlinarith

            -- case 4: a ≥ 2
            .
              simp at l3
              clear l2 l1
              rw [show |a + 1| = a + 1 by apply abs_of_nonneg; linarith] at h
              rw [show |a| = a by apply abs_of_nonneg; linarith] at h
              rw [show |a - 2| = a - 2 by apply abs_of_nonneg; linarith] at h
              nlinarith

      -- then we check the cases f x = -2 and a = 0 separately
      rcases o with o | o

      -- case 1: f x = -2
      .
        simp [a] at o
        clear h
        clear_value a
        simp [f] at o
        by_cases l1: x < -1

        -- case 1.1: x < -1
        .
          rw [show |x + 1| = -(x + 1) by apply abs_of_neg; linarith] at o
          rw [show |x| = -x by apply abs_of_neg; linarith] at o
          rw [show |x - 2| = -(x - 2) by apply abs_of_neg; linarith] at o
          nlinarith

        .
          simp at l1
          by_cases l2: x < 0

          -- case 1.2: -1 ≤ x < 0
          .
            rw [show |x + 1| = x + 1 by apply abs_of_nonneg; linarith] at o
            rw [show |x| = -x by apply abs_of_neg; linarith] at o
            rw [show |x - 2| = -(x - 2) by apply abs_of_neg; linarith] at o
            left
            nlinarith

          .
            simp at l2
            by_cases l3: x < 2
            .
              -- case 1.3: 0 ≤ x < 2
              rw [show |x + 1| = x + 1 by apply abs_of_nonneg; linarith] at o
              rw [show |x| = x by apply abs_of_nonneg; linarith] at o
              rw [show |x - 2| = -(x - 2) by apply abs_of_neg; linarith] at o
              nlinarith
            .
              -- case 1.4: x ≥ 2
              simp at l3
              clear l2 l1
              rw [show |x + 1| = x + 1 by apply abs_of_nonneg; linarith] at o
              rw [show |x| = x by apply abs_of_nonneg; linarith] at o
              rw [show |x - 2| = x - 2 by apply abs_of_nonneg; linarith] at o
              nlinarith

      -- case 2: f x = 0
      .
        simp [a] at o
        clear h
        clear_value a
        simp [f] at o
        by_cases l1: x < -1

        -- case 2.1: x < -1
        .
          rw [show |x + 1| = -(x + 1) by apply abs_of_neg; linarith] at o
          rw [show |x| = -x by apply abs_of_neg; linarith] at o
          rw [show |x - 2| = -(x - 2) by apply abs_of_neg; linarith] at o
          right
          left
          nlinarith

        .
          simp at l1
          by_cases l2: x < 0

          -- case 2.2: -1 ≤ x < 0
          .
            rw [show |x + 1| = x + 1 by apply abs_of_nonneg; linarith] at o
            rw [show |x| = -x by apply abs_of_neg; linarith] at o
            rw [show |x - 2| = -(x - 2) by apply abs_of_neg; linarith] at o
            nlinarith

          .
            simp at l2
            by_cases l3: x < 2

            -- case 2.3: 0 ≤ x < 2
            .
              rw [show |x + 1| = x + 1 by apply abs_of_nonneg; linarith] at o
              rw [show |x| = x by apply abs_of_nonneg; linarith] at o
              rw [show |x - 2| = -(x - 2) by apply abs_of_neg; linarith] at o
              right
              right
              nlinarith

            -- case 2.4: x ≥ 2
            .
              simp at l3
              clear l2 l1
              rw [show |x + 1| = x + 1 by apply abs_of_nonneg; linarith] at o
              rw [show |x| = x by apply abs_of_nonneg; linarith] at o
              rw [show |x - 2| = x - 2 by apply abs_of_nonneg; linarith] at o
              nlinarith


    -- the right to left direction
    .
      intro h
      simp at h
      rcases h with h | h | h
      .
        simp [h, f]
        norm_num
      .
        simp [h, f]
        norm_num
      .
        simp [h]
        have o: f 3⁻¹ = 0 := by
          simp [f]
          norm_num
          rw [show |(4 / 3: ℝ)| = 4 / 3 by apply abs_of_nonneg; norm_num]
          rw [show |(1 / 3: ℝ)| = 1 / 3 by apply abs_of_nonneg; norm_num]
          rw [show |(5 / 3: ℝ)| = 5 / 3 by apply abs_of_nonneg; norm_num]
          norm_num
        rw [o]
        simp [f]
        norm_num


  -- then we count the number of solutions
  rw [h_eq]
  repeat rw [Set.encard_insert_of_not_mem]
  simp
  norm_num
  simp
  norm_num
  simp
  norm_num