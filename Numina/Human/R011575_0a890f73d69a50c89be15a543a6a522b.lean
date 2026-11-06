import Mathlib

-- prove a simple identity
lemma lemma_1 (x: ℝ) (hx: ¬3 - x = 0):
  (x ^ 2 - 7 * x + 12) / (3 - x) = 4 - x := by
  field_simp
  ring

/-Find all values of the parameter a, for each of which the equation
 a * |x - 1| = (x ^ 2 - 7 * x + 12) / (3 - x)
 has exactly one solution.-/

theorem algebra_144492:
  {a: ℝ | ∃! x, 3 - x ≠ 0 ∧ a * |x - 1| + (x ^ 2 - 7 * x + 12) / (3 - x) = 0}
  = Set.Ico (-1) (-1 / 2) ∪ Set.Ioo (-1 / 2) 1 := by

  ext a
  simp only [Set.mem_setOf_eq]
  constructor

  -- the forward direction
  .
    intro h
    by_contra! l

    -- we simplify the hypothesis
    replace l: a < -1 ∨ a = -1 / 2 ∨ 1 ≤ a := by
      simp at l
      by_cases l1: a < -1
      .
        left
        exact l1
      .
        simp at l1
        simp [l1] at l
        right
        by_cases l2: a = -1 / 2
        .
          left
          exact l2
        .
          rcases l with ⟨l3, l4⟩
          have o: -1 / 2 < a := by
            by_contra! o
            replace o: a = -1 / 2 := by
              linarith
            simp [o] at l2
          simp [o] at l4
          right
          exact l4

    -- we prove one by one
    rcases l with l | l | l

    --case 1: a < -1
    .
      -- we show that there are two solution
      obtain ⟨x, hx, h⟩ := h
      clear hx
      let x1:= (a + 4) / (a + 1)
      let x2:= (a - 4) / (a - 1)
      have o1: a + 1 ≠ 0 := by
        by_contra! o1
        simp [o1] at l
        linarith
      have o2: a - 1 ≠ 0 := by
        by_contra! o2
        simp [o2] at l
        linarith
      have n1: ¬ 3 - x1 = 0 := by
        by_contra! n1
        simp [x1] at n1
        field_simp at n1
        nlinarith [n1, l]
      have n2: ¬ 3 - x2 = 0 := by
        by_contra! n2
        simp [x2] at n2
        field_simp at n2
        nlinarith [n2, l]
      have f1: a * |x1 - 1| + (x1 ^ 2 - 7 * x1 + 12) / (3 - x1) = 0 := by
        rw [lemma_1 x1 n1]
        have g1: x1 ≤ 1 := by
          simp [x1]
          rw [div_le_one_of_neg]
          linarith
          linarith
        rw [show |x1 - 1| = -(x1 - 1) by apply abs_of_nonpos; linarith]
        simp [x1]
        field_simp
        ring
      have f2: a * |x2 - 1| + (x2 ^ 2 - 7 * x2 + 12) / (3 - x2) = 0 := by
        rw [lemma_1 x2 n2]
        have g2: 1 ≤ x2 := by
          simp [x2]
          rw [one_le_div_of_neg]
          linarith
          linarith
        rw [show |x2 - 1| = x2 - 1 by apply abs_of_nonneg; linarith]
        simp [x2]
        field_simp
        ring
      have h1:= h x1
      simp [n1, f1] at h1
      have h2:= h x2
      simp [n2, f2] at h2
      rw [← h2] at h1
      simp [x1, x2] at h1
      field_simp at h1
      replace h1: a = -1 / 2 := by
        linarith
      simp [h1] at l
      norm_num at l

    --case 2: a = -1 / 2
    .
      -- we show that there are no solution
      obtain ⟨x, hx, h⟩ := h
      clear h
      rcases hx with ⟨hx, h⟩
      rw [lemma_1 x hx] at h
      simp [l] at h
      by_cases lx: 1 ≤ x
      .
        rw [show |x - 1| = x - 1 by apply abs_of_nonneg; linarith] at h
        ring_nf at h
        replace h: x = 3 := by linarith
        simp [h] at hx
      .
        rw [show |x - 1| = -(x - 1) by apply abs_of_nonpos; linarith] at h
        ring_nf at h
        replace h: x = 7 := by linarith
        simp [h] at lx

    --case 3: 1 ≤ a
    .
      -- we show that there are no solution
      obtain ⟨x, hx, h⟩ := h
      clear h
      rcases hx with ⟨hx, h⟩
      rw [lemma_1 x hx] at h
      by_cases lx: 1 ≤ x
      .
        rw [show |x - 1| = x - 1 by apply abs_of_nonneg; linarith] at h
        ring_nf at h
        nlinarith
      .
        rw [show |x - 1| = -(x - 1) by apply abs_of_nonpos; linarith] at h
        ring_nf at h
        nlinarith

  -- the backward direction
  .
    intro h
    simp at h
    rcases h with h | h

    -- case 1: a ∈ Set.Ico (-1) (-1 / 2)
    .
      rcases h with ⟨l, r⟩
      set y:= (a - 4) / (a - 1)
      have o: a - 1 ≠ 0 := by
        by_contra! o
        replace o: a = 1 := by
          linarith
        simp [o] at l
        linarith
      have n: ¬ 3 - y = 0 := by
        by_contra! n
        simp [y] at n
        field_simp at n
        nlinarith
      have f1: a * |y - 1| + (y ^ 2 - 7 * y + 12) / (3 - y) = 0 := by
        rw [lemma_1 y n]
        have g1: 1 ≤ y := by
          simp [y]
          rw [one_le_div_of_neg]
          linarith
          linarith
        rw [show |y - 1| = y - 1 by apply abs_of_nonneg; linarith]
        simp [y]
        field_simp
        ring
      use y
      simp [n, f1]
      intro y1 s
      rw [lemma_1 y1 s]
      intro u
      by_cases l1: 1 ≤ y1
      .
        rw [show |y1 - 1| = y1 - 1 by apply abs_of_nonneg; linarith] at u
        ring_nf at u
        simp [y]
        field_simp
        linarith
      .
        simp at l1
        rw [show |y1 - 1| = -(y1 - 1) by apply abs_of_nonpos; linarith] at u
        nlinarith

    -- case 2: a ∈ Set.Ioo (-1 / 2) 1
    .
      rcases h with ⟨l, r⟩
      set y:= (a - 4) / (a - 1)
      have o: a - 1 ≠ 0 := by
        by_contra! o
        replace o: a = 1 := by
          linarith
        simp [o] at l
        linarith
      have n: ¬ 3 - y = 0 := by
        by_contra! n
        simp [y] at n
        field_simp at n
        nlinarith
      have f1: a * |y - 1| + (y ^ 2 - 7 * y + 12) / (3 - y) = 0 := by
        rw [lemma_1 y n]
        have g1: 1 ≤ y := by
          simp [y]
          rw [one_le_div_of_neg]
          linarith
          linarith
        rw [show |y - 1| = y - 1 by apply abs_of_nonneg; linarith]
        simp [y]
        field_simp
        ring
      use y
      simp [n, f1]
      intro y1 s
      rw [lemma_1 y1 s]
      intro u
      by_cases l1: 1 ≤ y1
      .
        rw [show |y1 - 1| = y1 - 1 by apply abs_of_nonneg; linarith] at u
        ring_nf at u
        simp [y]
        field_simp
        linarith
      .
        simp at l1
        rw [show |y1 - 1| = -(y1 - 1) by apply abs_of_nonpos; linarith] at u
        nlinarith
