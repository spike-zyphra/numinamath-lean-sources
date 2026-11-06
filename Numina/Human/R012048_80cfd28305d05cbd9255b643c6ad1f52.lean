import Mathlib

open Real

/-find x such that
0 < (log 7 - log (-8 * x - x ^ 2)) / log (x + 3)-/

theorem algebra_170868: {x: ℝ | 0 < x + 3 ∧ x + 3 ≠ 1 ∧ 0 < -8 * x - x ^ 2 ∧
  0 < (log 7 - log (-8 * x - x ^ 2)) / log (x + 3)} =
    Set.Ioo (-3) (-2) ∪ Set.Ioo (-1) 0 := by

  ext x
  simp only [Set.mem_setOf_eq]
  constructor

  -- the forward direction
  .
    intro h
    rcases h with ⟨l1, n, l2, h⟩
    replace l1: -3 < x := by
      linarith
    replace l2: x < 0 := by
      nlinarith
    simp
    by_cases r: x < -2
    .
      left
      constructor
      .
        linarith
      .
        linarith
    .
      -- -2 < x
      replace r: -2 < x := by
        by_contra! o
        simp at r
        have s: x = -2 := by
          linarith
        simp [s] at n
        norm_num at n
      clear l1
      right
      simp [l2]
      by_contra! l
      clear l2
      absurd h
      simp
      apply div_nonpos_of_nonpos_of_nonneg
      .
        have o: log 7 ≤ log (-(8 * x) - x ^ 2) := by
          apply Real.log_le_log
          norm_num
          nlinarith
        linarith
      .
        apply Real.log_nonneg
        linarith


  -- the backward direction
  .
    intro h
    simp at h
    rcases h with h | h
    .
      -- left
      rcases h with ⟨l1, l2⟩
      have r: 0 < x + 3 := by
        linarith
      simp [r]
      have r': ¬ x + 3 = 1 := by
        by_contra! o
        replace o: x = -2 := by
          linarith
        simp [o] at l2
      simp [r']
      clear r r'
      constructor
      .
        nlinarith
      .
        apply div_pos_of_neg_of_neg
        .
          have r: log 7 < log (-(8 * x) - x ^ 2) := by
            apply Real.log_lt_log
            norm_num
            nlinarith
          linarith
        .
          apply Real.log_neg
          linarith
          linarith
    .
      -- right
      rcases h with ⟨l1, l2⟩
      have r: 0 < x + 3 := by
        linarith
      simp [r]
      have r': ¬ x + 3 = 1 := by
        by_contra! o
        replace o: x = -2 := by
          linarith
        simp [o] at l1
      simp [r']
      clear r r'
      constructor
      .
        nlinarith
      .
        apply div_pos
        .
          have r: log (-(8 * x) - x ^ 2) < log 7:= by
            apply Real.log_lt_log
            norm_num
            nlinarith
            nlinarith
          linarith
        .
          apply Real.log_pos
          linarith