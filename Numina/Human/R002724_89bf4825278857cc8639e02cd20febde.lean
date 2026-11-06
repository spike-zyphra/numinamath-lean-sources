import Mathlib

open Real

/-In the set of real numbers, solve the inequality:

$$
2|x-2|-\left|\frac{3}{|x-3|}-1\right| \geqslant 1
$$ -/

theorem inequalities_104610 (x : ℝ) (ne: x ≠ 3):
  (2 * abs (x - 2) - abs (3 / abs (x - 3) - 1)) ≥ 1 ↔
  (x ≤ (5 - sqrt 7) / 2 ∨ x ≥ (5 + sqrt 7) / 2) := by

  have g1: 2 < √7 := by
    apply Real.lt_sqrt_of_sq_lt
    norm_num
  have g2: √7 < 3 := by
    rw [Real.sqrt_lt']
    norm_num
    norm_num
  have g3: √7 ^ 2 = 7 := by
    symm
    rw [← Real.sqrt_eq_iff_eq_sq]
    norm_num
    apply sqrt_nonneg

  constructor

  -- the forward direction
  .
    intro h
    by_cases l1: x ≤ 2

    -- case x ≤ 2
    .
      left
      rw [show |x - 2| = - (x - 2) by apply abs_of_nonpos; linarith] at h
      rw [show |x - 3| = - (x - 3) by apply abs_of_nonpos; linarith] at h
      by_cases r: x ≤ 0
      .
        -- case x ≤ 0
        .
          nlinarith
      .
        simp at r
        have o: 3 / -(x - 3) - 1 = x / (3 - x) := by
          have o1: - (x - 3) ≠ 0 := by
            by_contra! o
            linarith
          have o2: 3 - x ≠ 0 := by
            by_contra! O
            linarith
          field_simp
        rw [o] at h
        clear o
        have o: |x / (3 - x)| = x / (3 - x) := by
          apply abs_of_nonneg
          apply div_nonneg
          linarith
          linarith
        rw [o] at h
        clear o
        have o2: 3 - x ≠ 0 := by
            by_contra! O
            linarith
        simp at h
        replace h: 0 ≤ 2 * (2 - x) - x / (3 - x) - 1 := by
          linarith
        have o3: 2 * (2 - x) - x / (3 - x) - 1 = (2 * x ^ 2 - 10 * x + 9) / (3 - x) := by
          field_simp
          ring
        rw [o3] at h
        clear o3
        rw [div_nonneg_iff] at h
        rcases h with h | h
        .
          rcases h with ⟨h, j⟩
          have g: 2 * x ^ 2 - 10 * x + 9 = 2 * (x - (5 + √7) / 2) * (x - (5 - √7) / 2) := by
            ring_nf
            simp [g3]
            ring
          rw [g] at h
          clear g
          by_contra! u
          absurd h
          simp
          apply mul_neg_of_neg_of_pos
          .
            nlinarith
          .
            clear *- u
            nlinarith
        .
          rcases h with ⟨i, j⟩
          absurd j
          simp
          linarith

    -- case 2 < x
    .
      simp at l1
      right
      rw [show |x - 2| = x - 2 by apply abs_of_nonneg; linarith] at h
      by_cases r: x ≤ 3

      -- case x < 3
      .
        rw [show |x - 3| = - (x - 3) by apply abs_of_nonpos; linarith] at h
        have o: 3 / -(x - 3) - 1 = x / (3 - x) := by
          have o1: - (x - 3) ≠ 0 := by
            by_contra! o
            absurd ne
            linarith
          have o2: 3 - x ≠ 0 := by
            by_contra! O
            absurd ne
            linarith
          field_simp
        rw [o] at h
        clear o
        have o: |x / (3 - x)| = x / (3 - x) := by
          apply abs_of_nonneg
          apply div_nonneg
          linarith
          linarith
        rw [o] at h
        clear o
        replace h: 0 ≤ 2 * (x - 2) - x / (3 - x) - 1 := by
          linarith
        have o3: 2 * (x - 2) - x / (3 - x) - 1 = (-2 * x ^ 2 + 10 * x - 15) / (3 - x) := by
          have o1: 3 - x ≠ 0 := by
            by_contra! o
            absurd ne
            linarith
          field_simp
          ring
        rw [o3] at h
        clear o3
        absurd h
        simp
        apply div_neg_of_neg_of_pos
        .
          nlinarith
        .
          by_contra! j
          have i: x = 3 := by linarith
          simp [i] at ne

      -- case 3 < x
      .
        simp at r
        clear l1 ne
        rw [show |x - 3| = x - 3 by apply abs_of_nonneg; linarith] at h
        have f: x - 3 ≠ 0 := by
          by_contra! o
          linarith
        have o: 3 / (x - 3) - 1 = (6 - x) / (x - 3) := by
          field_simp
          ring
        rw [o] at h
        clear o
        by_cases u: x ≤ 6

        -- case x ≤ 6
        .
          have j: |(6 - x) / (x - 3)|= (6 - x) / (x - 3) := by
            apply abs_of_nonneg
            apply div_nonneg
            linarith
            linarith
          rw [j] at h
          clear j
          replace h: 0 ≤ 2 * (x - 2) - (6 - x) / (x - 3) - 1 := by
            linarith
          have j: 2 * (x - 2) - (6 - x) / (x - 3) - 1 = (2 * x ^ 2 - 10 * x + 9) / (x - 3) := by
            field_simp
            ring
          rw [j] at h
          clear j
          rw [div_nonneg_iff] at h
          rcases h with h | h
          .
            rcases h with ⟨h, i⟩
            nlinarith
          .
            rcases h with ⟨h, i⟩
            absurd i
            linarith

        -- case 6 < x
        .
          simp at u
          clear h
          nlinarith

  -- the backward direction
  .
    intro h
    have f: x - 3 ≠ 0 := by
      by_contra! o
      absurd ne
      linarith
    have m: 3 - x ≠ 0 := by
        by_contra! o
        absurd ne
        linarith
    rcases h with h | h

    .
      have l: x ≤ 2 := by
        nlinarith
      rw [show |x - 2| = -(x - 2) by apply abs_of_nonpos; linarith]
      rw [show |x - 3| = -(x - 3) by apply abs_of_nonpos; linarith]
      have j: 3 / -(x - 3) - 1 = x / (3 - x) := by
        have o: 3 - x ≠ 0 := by
          by_contra! o
          absurd ne
          linarith
        field_simp
      rw [j]
      clear j
      by_cases s: x < 0
      .
        have o: |x / (3 - x)| = -(x / (3 - x)) := by
          apply abs_of_nonpos
          apply div_nonpos_of_nonpos_of_nonneg
          linarith
          linarith
        rw [o]
        clear o
        suffices 0 ≤ 2 * -(x - 2) - -(x / (3 - x)) - 1 by
          linarith
        have o: 2 * -(x - 2) - -(x / (3 - x)) - 1 = (2 * x ^ 2 - 8 * x + 9) / (3 - x) := by
          field_simp
          ring
        rw [o]
        clear o
        apply div_nonneg
        .
          nlinarith
        .
          linarith

      -- cases 0 ≤ x
      .
        simp at s
        have o: |x / (3 - x)| = (x / (3 - x)) := by
          apply abs_of_nonneg
          apply div_nonneg
          linarith
          linarith
        rw [o]
        clear o
        suffices 0 ≤ 2 * -(x - 2) - x / (3 - x) - 1 by
          linarith
        have o: 2 * -(x - 2) - x / (3 - x) - 1 = (2 * x ^ 2 - 10 * x + 9) / (3 - x) := by
          field_simp
          ring
        rw [o]
        clear o
        apply div_nonneg
        .
          nlinarith
        .
          linarith

    .
      have l: 3 ≤ x := by
        nlinarith
      rw [show |x - 2| = (x - 2) by apply abs_of_nonneg; linarith]
      rw [show |x - 3| = (x - 3) by apply abs_of_nonneg; linarith]
      have j: 3 / (x - 3) - 1 = (6 - x) / (x - 3) := by
        field_simp
        ring
      rw [j]
      clear j
      by_cases s: 6 < x
      .
        have o: |(6 - x) / (x - 3)| = - ((6 - x) / (x - 3)) := by
          apply abs_of_nonpos
          apply div_nonpos_of_nonpos_of_nonneg
          linarith
          linarith
        rw [o]
        clear o
        suffices 0 ≤ 2 * (x - 2) - -((6 - x) / (x - 3)) - 1 by
          linarith
        have o: 2 * (x - 2) - -((6 - x) / (x - 3)) - 1 = (2 * x ^ 2 - 12 * x + 21) / (x - 3) := by
          field_simp
          ring
        rw [o]
        clear o
        apply div_nonneg
        .
          nlinarith
        .
          linarith

      -- cases 0 ≤ x
      .
        simp at s
        have o: |(6 - x) / (x - 3)| = (6 - x) / (x - 3) := by
          apply abs_of_nonneg
          apply div_nonneg
          linarith
          linarith
        rw [o]
        clear o
        suffices 0 ≤ 2 * (x - 2) - (6 - x) / (x - 3) - 1 by
          linarith
        have o: 2 * (x - 2) - (6 - x) / (x - 3) - 1 = (2 * x ^ 2 - 10 * x + 9) / (x - 3) := by
          field_simp
          ring
        rw [o]
        clear o
        apply div_nonneg
        .
          nlinarith
        .
          linarith
