import Mathlib

open Real

-- we prove a lemma to simplify the condition
lemma lemma_1 (x k: ℝ) (hx: x ^ 2 - x ≠ 0): (x + 7) / (x - 1) + 1 / x - (4 * x + k) / (x ^ 2 - x) = 0
  ↔ (x + 2) ^ 2 = k + 5 := by
    constructor

    -- the forward direction
    .
      intro h
      rw [show x ^ 2 - x = x * (x - 1) by ring] at hx
      have o1: x - 1 ≠ 0 := by
        by_contra! o
        simp [o] at hx
      have o2: x ≠ 0 := by
        by_contra! o
        simp [o] at hx
      rw [show x * (x - 1) = x ^ 2 - x by ring] at hx
      field_simp at h
      ring_nf at h
      rw [show x + x * k + (-(x ^ 2 * 5) - x ^ 2 * k) + x ^ 3 * 3 + x ^ 4 =
         (x ^ 2 - x) * (x ^ 2 + 4 * x - (k + 1)) by ring] at h
      simp [hx] at h
      nlinarith

    -- the backward direction
    .
      intro h
      field_simp
      rw [show x ^ 2 - x = x * (x - 1) by ring] at hx
      have o1: x - 1 ≠ 0 := by
        by_contra! o
        simp [o] at hx
      have o2: x ≠ 0 := by
        by_contra! o
        simp [o] at hx
      field_simp
      ring_nf
      rw [show x + x * k + (-(x ^ 2 * 5) - x ^ 2 * k) + x ^ 3 * 3 + x ^ 4 =
         (x ^ 2 - x) * ((x + 2) ^ 2 - (k + 5)) by ring]
      simp [h]


/-If the equation
(x + 7) / (x - 1) + 1 / x - (4 * x + k) / (x ^ 2 - x) = 0
has only one real root (counting repeated roots as one).
Then the value of k is ( ).
(A) -5 (B) -1 or 4 (C) -5 or -1 (D) -5 or -1 or 4
-/

theorem algebra_308277: {k: ℝ | ∃! x, x ^ 2 - x ≠ 0 ∧ (x + 7) / (x - 1) + 1 / x - (4 * x + k) / (x ^ 2 - x) = 0}
  = {-5, -1, 4} := by

  ext k
  constructor

  -- the forward direction
  .
    intro h
    simp only [Set.mem_setOf_eq] at h
    simp
    obtain ⟨x, hx, h⟩ := h
    rcases hx with ⟨nx, hx⟩
    by_contra! n
    by_cases l: k < -5

    -- case 1: k < -5, we show there are no solution
    .
      clear h n
      rw [lemma_1 x k nx] at hx
      nlinarith

    -- case 2: k ≥ -5, we show there are two solutions
    .
      clear nx hx
      simp at l
      replace l: -5 < k := by
        by_contra! s
        have o: k = -5 := by linarith
        simp [o] at n
      rcases n with ⟨n3, n1, n2⟩
      clear n3
      set x1:= -2 + √(k + 5)
      set x2:= -2 - √(k + 5)
      -- we show that x1 and x2 are solutions
      have f1: x1 ^ 2 - x1 ≠ 0 := by
        by_contra! o
        rw [show x1 ^ 2 - x1 = x1 * (x1 - 1) by ring] at o
        simp at o
        rcases o with o | o
        .
          simp [x1] at o
          replace o: √(k + 5) = 2 := by linarith
          rw [Real.sqrt_eq_iff_mul_self_eq_of_pos] at o
          replace o: k = -1 := by linarith
          simp [o] at n1
          norm_num
        .
          simp [x1] at o
          replace o: √(k + 5) = 3 := by linarith
          rw [Real.sqrt_eq_iff_mul_self_eq_of_pos] at o
          replace o: k = 4 := by linarith
          simp [o] at n2
          norm_num
      have f2: x2 ^ 2 - x2 ≠ 0 := by
        by_contra! o
        rw [show x2 ^ 2 - x2 = x2 * (x2 - 1) by ring] at o
        simp at o
        rcases o with o | o
        .
          simp [x2] at o
          replace o: √(k + 5) = -2 := by linarith
          have s: 0 ≤ -2 := by
            rify
            rw [← o]
            apply Real.sqrt_nonneg
          norm_num at s
        .
          simp [x2] at o
          replace o: √(k + 5) = -3 := by linarith
          have c: 0 ≤ -3 := by
            rify
            rw [← o]
            apply Real.sqrt_nonneg
          norm_num at c
      have u1:= h x1
      simp [f1] at u1
      rw [show x1⁻¹ = 1 / x1 by simp] at u1
      rw [lemma_1 x1 k f1] at u1
      have g1: (x1 + 2) ^ 2 = k + 5 := by
        simp [x1]
        symm
        rw [← Real.sqrt_eq_iff_eq_sq]
        linarith
        apply Real.sqrt_nonneg
      simp [g1] at u1
      have u2:= h x2
      simp [f2] at u2
      rw [show x2⁻¹ = 1 / x2 by simp] at u2
      rw [lemma_1 x2 k f2] at u2
      have g2: (x2 + 2) ^ 2 = k + 5 := by
        simp [x2]
        symm
        ring_nf
        rw [← Real.sqrt_eq_iff_eq_sq]
        linarith
        apply Real.sqrt_nonneg
      simp [g2] at u2
      rw [← u2] at u1
      simp [x1, x2] at u1
      replace u1: √(k + 5) = 0 := by linarith
      rw [Real.sqrt_eq_zero] at u1
      replace u1: k = -5 := by linarith
      simp [u1] at l
      linarith


  -- the backward direction
  .
    intro h
    simp at h
    rcases h with h | h | h

    -- k = -5
    .
      simp [h]
      use -2
      constructor
      .
        simp
        norm_num
      .
        intro y h
        rcases h with ⟨hy, h⟩
        rw [show y⁻¹ = 1 / y by simp] at h
        rw [lemma_1 y (-5) hy] at h
        nlinarith

    -- k = -1
    .
      simp [h]
      use -4
      constructor
      .
        simp
        norm_num
      .
        intro y h
        rcases h with ⟨hy, h⟩
        rw [show y⁻¹ = 1 / y by simp] at h
        rw [lemma_1 y (-1) hy] at h
        replace h: y * (y + 4) = 0 := by nlinarith
        simp at h
        rcases h with h | h
        .
          simp [h] at hy
        .
          linarith

    -- k = 4
    .
      simp [h]
      use -5
      constructor
      .
        simp
        norm_num
      .
        intro y h
        rcases h with ⟨hy, h⟩
        rw [show y⁻¹ = 1 / y by simp] at h
        rw [lemma_1 y 4 hy] at h
        replace h: (y - 1)* (y + 5) = 0 := by nlinarith
        simp at h
        rcases h with h | h
        .
          replace h: y = 1 := by linarith
          simp [h] at hy
        .
          linarith