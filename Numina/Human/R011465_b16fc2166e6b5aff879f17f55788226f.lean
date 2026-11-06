import Mathlib

-- we write a lemma to simplify the left hand side of the equation
lemma lemma_1 (a: ℝ) (x: ℝ) (h1: 4 - x ^ 2 - a ≠ 0) (h2: 3 * a + 2 * x + 5 ≠ 0):
  (-(4*x^4) - (6*a + 10)*x^3 + (16 - 4*a)*x^2 - (6*a^2 - 14*a - 40)*x) /
  ((4 - x^2 - a) * (3*a + 2*x + 5)) = 2 * x := by
    field_simp
    ring

-- we write a lemma to simplify the right hand side of the equation
lemma lemma_2 (a: ℝ): √(a ^ 2 - 2 * a + 1) = |a - 1| := by
    rw [show a ^ 2 - 2 * a + 1 = (a - 1) ^ 2 by ring]
    rw [Real.sqrt_sq_eq_abs]

/-For what values of the parameter a does the equation
|(-4*x^4 - (6*a + 10)*x^3 + (16 - 4*a)*x^2 - (6*a^2 - 14*a - 40)*x) /
  ((4 - x^2 - a) * (3*a + 2*x + 5))| = √(a ^ 2 - 2 * a + 1)
  have one solution ?-/

theorem algebra_259485:
  {a: ℝ | ∃! x,  4 - x ^ 2 - a ≠ 0 ∧ 3 * a + 2 * x + 5 ≠ 0 ∧
    |(-(4*x^4) - (6*a + 10)*x^3 + (16 - 4*a)*x^2 - (6*a^2 - 14*a - 40)*x) /
  ((4 - x^2 - a) * (3*a + 2*x + 5))| = √(a ^ 2 - 2 * a + 1)}
  = {-3, -1, 1} := by

  ext a
  simp only [Set.mem_setOf_eq]
  constructor

  -- the forward direction
  .
    intro h
    obtain ⟨x, hx, h⟩ := h
    rcases hx with ⟨h1, h2, hx⟩
    rw [lemma_1] at hx
    rw [lemma_2] at hx h
    .
      simp
      rw [abs_eq_abs] at hx
      by_contra! l

      set x1:= (a - 1) / 2
      set x2:= - (a - 1) / 2
      by_cases l2: a ≠ 3 ∧ a ≠ -5
      .
        -- case 1: a ≠ 3 ∧ a ≠ -5, then we show there are two solutions: x1 and x2
        have f1:= h x1 -- first one
        have f2:= h x2 -- second one
        simp at f1 f2
        clear h

        have o1: ¬ 4 - x1 ^ 2 - a = 0 := by
          by_contra! o
          simp [x1] at o
          field_simp at o
          ring_nf at o
          rw [show 15 + (-(a * 2) - a ^ 2) = -(a - 3) * (a + 5) by ring] at o
          simp at o
          rcases o with o | o
          .
            replace o: a = 3 := by linarith
            simp [o] at l2
          .
            replace o: a = -5 := by linarith
            simp [o] at l2
        simp [o1] at f1
        have o2: ¬3 * a + 2 * x1 + 5 = 0 := by
          by_contra! o
          simp [x1] at o
          field_simp at o
          ring_nf at o
          replace o: a = -1 := by linarith
          simp [o] at l
        simp [o2] at f1
        have e: (-(4 * x1 ^ 4) - (6 * a + 10) * x1 ^ 3 + (16 - 4 * a) * x1 ^ 2 - (6 * a ^ 2 - 14 * a - 40) * x1) /
        ((4 - x1 ^ 2 - a) * (3 * a + 2 * x1 + 5)) = 2 * x1 := by
          rw [lemma_1]
          by_contra! t
          simp [t] at o1
          by_contra! z
          simp [z] at o2
        rw [e] at f1
        clear e
        simp [x1] at f1
        field_simp at f1

        have o1: ¬ 4 - x2 ^ 2 - a = 0 := by
          by_contra! o
          simp [x2] at o
          field_simp at o
          ring_nf at o
          rw [show 15 + (-(a * 2) - a ^ 2) = -(a - 3) * (a + 5) by ring] at o
          simp at o
          rcases o with o | o
          .
            replace o: a = 3 := by linarith
            simp [o] at l2
          .
            replace o: a = -5 := by linarith
            simp [o] at l2
        simp [o1] at f2
        have o2: ¬3 * a + 2 * x2 + 5 = 0 := by
          by_contra! o
          simp [x2] at o
          field_simp at o
          ring_nf at o
          replace o: a = -3 := by linarith
          simp [o] at l
        simp [o2] at f2
        have e: (-(4 * x2 ^ 4) - (6 * a + 10) * x2 ^ 3 + (16 - 4 * a) * x2 ^ 2 - (6 * a ^ 2 - 14 * a - 40) * x2) /
        ((4 - x2 ^ 2 - a) * (3 * a + 2 * x2 + 5)) = 2 * x2 := by
          field_simp
          ring
        rw [e] at f2
        clear e
        simp [x2] at f2
        field_simp at f2
        have v: |1 - a| = |a - 1| := by
          rw [← abs_neg]
          simp
        simp [v] at f2
        rw [← f2] at f1
        have t: a = 1 := by linarith
        simp [t] at l

      -- case 2: a = 3 ∨ a = -5, then we show there' s no solution
      .
        clear h
        simp at l2
        by_cases l3: a = 3
        .
          simp [l3] at hx
          rcases hx with i | i
          .
            replace i: x = 1 := by linarith
            simp [i, l3] at h1
            norm_num at h1
          .
            replace i: x = -1 := by linarith
            simp [i, l3] at h1
            norm_num at h1
        .
          simp [l3] at l2
          simp [l2] at hx
          rcases hx with i | i
          .
            replace i: x = -3 := by linarith
            simp [i, l3] at h1
            norm_num at h1
            simp [l2] at h1
          .
            replace i: x = 3 := by linarith
            simp [i, l3] at h1
            norm_num at h1
            simp [l2] at h1

    exact h1
    exact h2


  -- the backward direction
  .
    intro h
    simp at h
    rcases h with h | h | h

    -- a = -3
    .
      use -2
      constructor
      .
        simp [h]
        norm_num
        symm
        rw [Real.sqrt_eq_iff_mul_self_eq_of_pos]
        norm_num
        norm_num
      .
        simp
        intro y n1 n2 hy
        rw [lemma_1 a y n1 n2] at hy
        rw [lemma_2 a] at hy
        rw [abs_eq_abs] at hy
        simp [h] at hy
        rcases hy with i | i
        .
          linarith
        .
          replace i: y = 2 := by linarith
          simp [h, i] at n2
          norm_num at n2

    -- a = -1
    .
      use 1
      constructor
      .
        simp [h]
        norm_num
        symm
        rw [Real.sqrt_eq_iff_mul_self_eq_of_pos]
        norm_num
        norm_num
      .
        simp
        intro y n1 n2 hy
        rw [lemma_1 a y n1 n2] at hy
        rw [lemma_2 a] at hy
        rw [abs_eq_abs] at hy
        simp [h] at hy
        rcases hy with i | i
        .
          replace i: y = -1 := by linarith
          simp [h, i] at n2
          norm_num at n2
        .
          linarith

    -- a = 1
    .
      use 0
      constructor
      .
        simp [h]
        norm_num
      .
        simp
        intro y n1 n2 hy
        rw [lemma_1 a y n1 n2] at hy
        rw [lemma_2 a] at hy
        rw [abs_eq_abs] at hy
        simp [h] at hy
        exact hy
        
