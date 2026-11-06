import Mathlib

/- Find all real numbers $a$ for which the equation

$$
x^{2}+(a-2) x+1=3|x|
$$

has exactly three distinct real solutions in $x$.. -/

theorem algebra_123842: {a: ℝ | {x: ℝ | x ^ 2 + (a - 2) * x + 1 = 3 * |x|}.encard = 3} = {1, 3} := by

  ext a
  constructor

  -- the forward direction
  .
    intro h
    simp at h
    simp
    by_contra! n
    set s:= {x | x ^ 2 + (a - 2) * x + 1 = 3 * |x|}
    have u: a < 1 ∨ (1 < a ∧ a < 3) ∨ (3 < a) := by
      by_cases r: a < 1
      .
        left
        tauto
      .
        right
        by_cases l: a < 3
        .
          left
          simp at r
          refine ⟨?_, l⟩
          by_contra! o
          replace o: a = 1 := by linarith
          tauto
        .
          right
          simp at l
          by_contra! o
          replace o: a = 3 := by linarith
          tauto
    rcases u with u | u | u

    -- case a < 1
    .
      -- we show that s.encard ≤ 2
      set x3:= (5 - a - √(a ^ 2 - 10 * a + 21)) / 2
      set x4:= (5 - a + √(a ^ 2 - 10 * a + 21)) / 2
      set t: Set ℝ := {x3, x4}
      have o: s ⊆ t := by
        intro x hx
        simp [s] at hx
        simp [t]
        by_cases l: x < 0

        -- case x < 0, we show there are no solution
        .
          rw [show |x| = -x by apply abs_of_nonpos; linarith] at hx
          clear n h t
          clear_value x3 x4 s
          replace hx: (1 - a) * x = (x + 1) ^ 2 := by
            nlinarith
          have o: 0 ≤ (1 - a) * x := by
            rw [hx]
            nlinarith
          absurd o
          simp
          nlinarith

        -- case 0 ≤ x, then x = x3 or x4
        .
          rw [show |x| = x by apply abs_of_nonneg; linarith] at hx
          simp at l
          clear n h t
          clear_value s
          replace hx: (2 * x + (a - 5)) ^ 2 = (a - 5) ^ 2 - 4 := by
            nlinarith
          symm at hx
          by_cases r: 0 ≤ 2 * x + (a - 5)
          .
            rw [← Real.sqrt_eq_iff_eq_sq] at hx
            ring_nf at hx
            right
            simp [x4]
            ring_nf
            nlinarith
            nlinarith
            tauto
          .
            simp at r
            rw [show (2 * x + (a - 5)) ^ 2 = (-(2 * x + (a - 5))) ^ 2 by ring] at hx
            rw [← Real.sqrt_eq_iff_eq_sq] at hx
            ring_nf at hx
            left
            simp [x3]
            ring_nf
            nlinarith
            nlinarith
            linarith
      have i: t.encard = 1 ∨ t.encard = 2 := by
        by_cases i: x3 = x4
        .
          left
          simp [t]
          rw [i]
          simp
        .
          right
          simp [t]
          rw [Set.encard_insert_of_not_mem]
          simp
          norm_num
          simp
          tauto
      have j: t.encard ≤ s.encard := by
        rcases i with i | i
        .
          simp [i, h]
        .
          simp [i, h]
          norm_num
      apply Set.Finite.eq_of_subset_of_encard_le at o
      simp [j] at o
      rw [o] at h
      rw [h] at i
      norm_num at i
      apply Set.Finite.subset at o
      rcases i with i | i
      .
        exact Set.finite_of_encard_eq_coe i
      .
        exact Set.finite_of_encard_eq_coe i
      
      rcases i with i | i
      .
        exact Set.finite_of_encard_eq_coe i
      .
        exact Set.finite_of_encard_eq_coe i


    -- case 1 < a < 3
    .
      -- we show that there are 4 solutions
      clear n
      set x1:= (-a - 1 - √(a ^ 2 + 2 * a - 3)) / 2
      set x2:= (-a - 1 + √(a ^ 2 + 2 * a - 3)) / 2
      set x3:= (5 - a - √(a ^ 2 - 10 * a + 21)) / 2
      set x4:= (5 - a + √(a ^ 2 - 10 * a + 21)) / 2
      have l1: x1 < x2 := by
        simp [x1, x2]
        have u: 0 < √(a ^ 2 + 2 * a - 3) := by
          apply Real.sqrt_pos_of_pos
          nlinarith
        linarith
      have l2: x2 < 0 := by
        simp [x2]
        suffices √(a ^ 2 + 2 * a - 3) < a + 1 by linarith
        rw [Real.sqrt_lt']
        nlinarith
        linarith
      have l3: 0 < x3 := by
        simp [x3]
        rw [Real.sqrt_lt']
        nlinarith
        linarith
      have l4: x3 < x4 := by
        simp [x3, x4]
        suffices 0 < √(a ^ 2 - 10 * a + 21) by linarith
        apply Real.sqrt_pos_of_pos
        nlinarith
      have p1: √(-3 + a * 2 + a ^ 2) ^ 2 = -3 + a * 2 + a ^ 2 := by
        symm
        rw [← Real.sqrt_eq_iff_eq_sq]
        nlinarith
        apply Real.sqrt_nonneg
      have p2: √(21 - a * 10 + a ^ 2) ^ 2 = 21 - a * 10 + a ^ 2 := by
        symm
        rw [← Real.sqrt_eq_iff_eq_sq]
        nlinarith
        apply Real.sqrt_nonneg
      set t: Set ℝ:= {x1, x2, x3, x4}
      have o: t ⊆ s := by
        intro x hx
        simp [t] at hx
        simp [s]
        rcases hx with v | v | v | v
        .
          rw [v]
          rw [show |x1| = -x1 by apply abs_of_nonpos; linarith]
          simp [x1]
          ring_nf
          simp [p1]
          ring
        .
          rw [v]
          rw [show |x2| = -x2 by apply abs_of_nonpos; linarith]
          simp [x2]
          ring_nf
          simp [p1]
          ring
        .
          rw [v]
          rw [show |x3| = x3 by apply abs_of_nonneg; linarith]
          simp [x3]
          ring_nf
          simp [p2]
          ring
        .
          rw [v]
          rw [show |x4| = x4 by apply abs_of_nonneg; linarith]
          simp [x4]
          ring_nf
          simp [p2]
          ring
      have ht: t.encard = 4 := by
        clear *- l1 l2 l3 l4
        simp [t]
        repeat rw [Set.encard_insert_of_not_mem]
        simp
        norm_num
        simp
        linarith
        simp
        refine ⟨(by linarith), (by linarith)⟩
        simp
        refine ⟨(by linarith), (by linarith), (by linarith)⟩
      have q: s.encard ≤ t.encard := by
        simp [ht, h]
        norm_num
      apply Set.Finite.eq_of_subset_of_encard_le at o
      simp [q] at o
      clear q
      rw [o] at ht
      rw [ht] at h
      norm_num at h
      exact Set.finite_of_encard_eq_coe h

  -- case 3 < a
    .
      -- we show that s.encard ≤ 2
      set x1:= (-a - 1 - √(a ^ 2 + 2 * a - 3)) / 2
      set x2:= (-a - 1 + √(a ^ 2 + 2 * a - 3)) / 2
      set t: Set ℝ := {x1, x2}
      have o: s ⊆ t := by
        intro x hx
        simp [s] at hx
        simp [t]
        by_cases l: 0 < x

        -- case 0 < x, we show there are no solution
        .
          rw [show |x| = x by apply abs_of_nonneg; linarith] at hx
          clear n h t
          clear_value x1 x2 s
          replace hx: (3 - a) * x = (x - 1) ^ 2 := by
            nlinarith
          have o: 0 ≤ (3 - a) * x := by
            rw [hx]
            nlinarith
          absurd o
          simp
          nlinarith

        -- case x ≤ 0, then x = x1 or x2
        .
          rw [show |x| = -x by apply abs_of_nonpos; linarith] at hx
          simp at l
          clear n h t
          clear_value s
          replace hx: (2 * x + (a + 1)) ^ 2 = (a + 1) ^ 2 - 4 := by
            nlinarith
          symm at hx
          by_cases r: 0 ≤ 2 * x + (a + 1)
          .
            rw [← Real.sqrt_eq_iff_eq_sq] at hx
            ring_nf at hx
            right
            simp [x2]
            ring_nf
            nlinarith
            nlinarith
            tauto
          .
            simp at r
            rw [show (2 * x + (a + 1)) ^ 2 = (-(2 * x + (a + 1))) ^ 2 by ring] at hx
            rw [← Real.sqrt_eq_iff_eq_sq] at hx
            ring_nf at hx
            left
            simp [x1]
            ring_nf
            nlinarith
            nlinarith
            linarith
      have i: t.encard = 1 ∨ t.encard = 2 := by
        by_cases i: x1 = x2
        .
          left
          simp [t]
          rw [i]
          simp
        .
          right
          simp [t]
          rw [Set.encard_insert_of_not_mem]
          simp
          norm_num
          simp
          tauto
      have j: t.encard ≤ s.encard := by
        rcases i with i | i
        .
          simp [i, h]
        .
          simp [i, h]
          norm_num
      apply Set.Finite.eq_of_subset_of_encard_le at o
      simp [j] at o
      rw [o] at h
      rw [h] at i
      norm_num at i
      apply Set.Finite.subset at o
      rcases i with i | i
      .
        exact Set.finite_of_encard_eq_coe i
      .
        exact Set.finite_of_encard_eq_coe i

      rcases i with i | i
      .
        exact Set.finite_of_encard_eq_coe i
      .
        exact Set.finite_of_encard_eq_coe i
      
      


  -- the backward direction
  .
    intro h
    simp at h
    rcases h with h | h

    -- case a = 1
    .
      simp [h]
      suffices {x: ℝ | x ^ 2 + (1 - 2) * x + 1 = 3 * |x|} = {-1, 2 - √3, 2 + √3} by
        have v: 0 < √3 := by
          apply Real.sqrt_pos_of_pos
          norm_num
        rw [this]
        repeat rw [Set.encard_insert_of_not_mem]
        simp
        norm_num
        simp
        linarith
        simp
        refine ⟨?_, (by linarith)⟩
        by_contra! o
        replace o: √3 = 3 := by linarith
        rw [Real.sqrt_eq_iff_mul_self_eq_of_pos] at o
        norm_num at o
        norm_num
      ext x
      constructor
      -- one direction
      .
        intro hx
        simp at hx
        simp
        by_cases l: x < 0

        -- case x < 0
        .
          left
          rw [show |x| = -x by apply abs_of_nonpos; linarith] at hx
          nlinarith

        -- case 0 ≤ x
        .
          right
          rw [show |x| = x by apply abs_of_nonneg; linarith] at hx
          simp at l
          replace hx: (x - 2) ^ 2 = 3 := by nlinarith
          symm at hx
          by_cases r: 0 < x - 2
          .
            rw [← Real.sqrt_eq_iff_eq_sq] at hx
            right
            linarith
            norm_num
            linarith
          .
            simp at r
            rw [show (x - 2) ^ 2 = (2 - x) ^ 2 by ring] at hx
            left
            rw [← Real.sqrt_eq_iff_eq_sq] at hx
            linarith
            norm_num
            linarith
      -- another direction
      .
        intro v
        simp at v
        have u: √3 ^ 2 = 3 := by
          symm
          rw [← Real.sqrt_eq_iff_eq_sq]
          norm_num
          norm_num
        rcases v with v | v | v
        .
          simp [v]
          norm_num
        .
          simp [v]
          ring_nf
          rw [u]
          have o: √3 < 2 := by
            rw [Real.sqrt_lt' ]
            norm_num
            norm_num
          rw [show |2 - √3| = 2 - √3 by apply abs_of_nonneg; linarith]
          ring
        .
          simp [v]
          ring_nf
          rw [u]
          have i: 0 ≤ √3 := by
            apply Real.sqrt_nonneg
          rw [show |2 + √3| = 2 + √3 by apply abs_of_nonneg; linarith]
          ring

    -- case a = 1
    .
      simp [h]
      suffices {x | x ^ 2 + (3 - 2) * x + 1 = 3 * |x|} = {-2 - √3, -2 + √3, 1} by
        have v: 0 < √3 := by
          apply Real.sqrt_pos_of_pos
          norm_num
        rw [this]
        repeat rw [Set.encard_insert_of_not_mem]
        simp
        norm_num
        simp
        by_contra! o
        replace o: √3 = 3 := by linarith
        rw [Real.sqrt_eq_iff_mul_self_eq_of_pos] at o
        norm_num at o
        norm_num
        simp
        refine ⟨(by linarith), (by linarith)⟩
      ext x
      constructor
      -- one direction
      .
        intro hx
        simp at hx
        simp
        by_cases l: 0 < x

        -- case 0 ≤ x
        .
          right
          right
          rw [show |x| = x by apply abs_of_nonneg; linarith] at hx
          nlinarith

        -- case x < 0
        .
          rw [show |x| = -x by apply abs_of_nonpos; linarith] at hx
          simp at l
          replace hx: (x + 2) ^ 2 = 3 := by nlinarith
          symm at hx
          by_cases r: 0 < x + 2
          .
            rw [← Real.sqrt_eq_iff_eq_sq] at hx
            right
            left
            linarith
            norm_num
            linarith
          .
            left
            simp at r
            rw [show (x + 2) ^ 2 = (-x - 2) ^ 2 by ring] at hx
            rw [← Real.sqrt_eq_iff_eq_sq] at hx
            linarith
            norm_num
            linarith
      -- another direction
      .
        intro v
        simp at v
        have u: √3 ^ 2 = 3 := by
          symm
          rw [← Real.sqrt_eq_iff_eq_sq]
          norm_num
          norm_num
        rcases v with v | v | v
        .
          simp [v]
          ring_nf
          rw [u]
          have o: 0 ≤ √3 := by
            apply Real.sqrt_nonneg
          rw [show |-2 - √3| = -(-2 - √3) by apply abs_of_nonpos; linarith]
          ring
        .
          simp [v]
          ring_nf
          rw [u]
          have o: √3 < 2 := by
            rw [Real.sqrt_lt' ]
            norm_num
            norm_num
          rw [show |-2 + √3| = -(-2 + √3) by apply abs_of_nonpos; linarith]
          ring
        .
         simp [v]
         norm_num
