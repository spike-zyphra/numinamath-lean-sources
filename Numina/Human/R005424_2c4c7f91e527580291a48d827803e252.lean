import Mathlib

-- we first show two simp numerical lemmas
lemma sq_of_sqrt_17: √17 ^ 2 = 17 := by
    symm
    rw [← Real.sqrt_eq_iff_eq_sq]
    norm_num
    apply Real.sqrt_nonneg

lemma sq_of_sqrt_2: √2 ^ 2 = 2 := by
    symm
    rw [← Real.sqrt_eq_iff_eq_sq]
    norm_num
    apply Real.sqrt_nonneg

-- we prove the key factoring lemma
lemma lemma_1 (x: ℝ): x ^ 2 * (x - 3) ^ 2 - (x ^ 2 - 1) * (x - 2) = (x ^ 2 - 5 * x + 2) * (x ^ 2 - 2 * x - 1) := by
  ring

/-The curves y=x^2(x−3)^2 and y=(x^2−1)(x−2)
intersect at a number of points in the real plane.
Determine the sum of the x-coordinates of these points of intersection.-/

theorem algebra_608240: ∑ᶠ x ∈ {x: ℝ | x ^ 2 * (x - 3) ^ 2 = (x ^ 2 - 1) * (x - 2)}, x = 7 := by

  -- directly compute the solutions of the equation
  have h_eq: {x: ℝ | x ^ 2 * (x - 3) ^ 2 = (x ^ 2 - 1) * (x - 2)} =
    {1 + √2, 1 - √2, 5 / 2 - √17 / 2, 5 / 2 + √17 / 2} := by
    ext x
    constructor

    -- the forward direction
    .
      intro h
      simp at h
      simp
      replace h: x ^ 2 * (x - 3) ^ 2 - (x ^ 2 - 1) * (x - 2) = 0 := by
        rw [h]
        simp
      rw [lemma_1] at h
      simp at h
      rcases h with h | h
      .
        have eq: x ^ 2 - 5 * x + 2 = (x - (5 / 2 - √17 / 2)) * (x - (5 / 2 + √17 / 2)) := by
          ring_nf
          rw [sq_of_sqrt_17]
          ring
        rw [eq] at h
        clear eq
        simp at h
        right
        right
        rcases h with h | h
        .
          left
          linarith
        .
          right
          linarith

      .
        have eq: x ^ 2 - 2 * x - 1 = (x - (1 + √2)) * (x - (1 - √2)) := by
          ring_nf
          rw [sq_of_sqrt_2]
          ring
        rw [eq] at h
        clear eq
        simp at h
        rcases h with h | h
        .
          left
          linarith
        .
          right
          left
          linarith


    -- the backward direction
    .
      intro h
      simp
      suffices x ^ 2 * (x - 3) ^ 2 - (x ^ 2 - 1) * (x - 2) = 0 by linarith
      rw [lemma_1]
      simp at h
      rcases h with h | h | h | h
      .
        suffices x ^ 2 - 2 * x - 1 = 0 by simp [this]
        have eq: x ^ 2 - 2 * x - 1 = (x - (1 + √2)) * (x - (1 - √2)) := by
          ring_nf
          rw [sq_of_sqrt_2]
          ring
        rw [eq]
        clear eq
        simp [h]
      .
        suffices x ^ 2 - 2 * x - 1 = 0 by simp [this]
        have eq: x ^ 2 - 2 * x - 1 = (x - (1 + √2)) * (x - (1 - √2)) := by
          ring_nf
          rw [sq_of_sqrt_2]
          ring
        rw [eq]
        clear eq
        simp [h]
      .
        suffices x ^ 2 - 5 * x + 2 = 0 by simp [this]
        have eq: x ^ 2 - 5 * x + 2 = (x - (5 / 2 - √17 / 2)) * (x - (5 / 2 + √17 / 2)) := by
          ring_nf
          rw [sq_of_sqrt_17]
          ring
        rw [eq]
        clear eq
        simp [h]
      .
        suffices x ^ 2 - 5 * x + 2 = 0 by simp [this]
        have eq: x ^ 2 - 5 * x + 2 = (x - (5 / 2 - √17 / 2)) * (x - (5 / 2 + √17 / 2)) := by
          ring_nf
          rw [sq_of_sqrt_17]
          ring
        rw [eq]
        clear eq
        simp [h]


  -- finally, we compute the sum
  rw [h_eq]
  rw [finsum_mem_eq_toFinset_sum]
  simp
  rw [Finset.sum_insert]
  rw [Finset.sum_insert]
  rw [Finset.sum_insert]
  rw [Finset.sum_singleton]

  ring

  -- need to verify the four points are distinct
  .
    simp
    by_contra! o
    replace o: √17 = 0 := by linarith
    norm_num at o
  .
    simp
    constructor
    .
      by_contra! o
      replace o: √17 - 2 * √2 = 3 := by linarith
      replace o: (√17 - 2 * √2) ^ 2 = 9 := by simp [o]; norm_num
      ring_nf at o
      simp [sq_of_sqrt_17, sq_of_sqrt_2] at o
      replace o: √2 * √17 = 4 := by linarith
      rw [show √2 * √17 = √34 by rw [← Real.sqrt_mul]; norm_num; linarith] at o
      rw [Real.sqrt_eq_iff_eq_sq] at o
      norm_num at o
      norm_num
      norm_num
    .
      by_contra! o
      replace o: √17 + 2 * √2 = -3 := by linarith
      replace o: (√17 + 2 * √2) ^ 2 = 9 := by simp [o]; norm_num
      ring_nf at o
      simp [sq_of_sqrt_17, sq_of_sqrt_2] at o
      replace o: √2 * √17 = -4 := by linarith
      rw [show √2 * √17 = √34 by rw [← Real.sqrt_mul]; norm_num; linarith] at o
      have p: 0 ≤ -4 := by
        rify
        rw [← o]
        apply Real.sqrt_nonneg
      norm_num at p
  .
    simp
    constructor
    .
      by_contra! o
      replace o: √2 = 0 := by linarith
      norm_num at o
    .
      constructor
      .
        by_contra! o
        replace o: √17 + 2 * √2 = 3 := by linarith
        replace o: (√17 + 2 * √2) ^ 2 = 9 := by simp [o]; norm_num
        ring_nf at o
        simp [sq_of_sqrt_17, sq_of_sqrt_2] at o
        replace o: √2 * √17 = -4 := by linarith
        rw [show √2 * √17 = √34 by rw [← Real.sqrt_mul]; norm_num; linarith] at o
        have p: 0 ≤ -4 := by
          rify
          rw [← o]
          apply Real.sqrt_nonneg
        norm_num at p
      .
        by_contra! o
        replace o: √17 - 2 * √2 = -3 := by linarith
        replace o: (√17 - 2 * √2) ^ 2 = 9 := by simp [o]; norm_num
        ring_nf at o
        simp [sq_of_sqrt_17, sq_of_sqrt_2] at o
        replace o: √2 * √17 = 4 := by linarith
        rw [show √2 * √17 = √34 by rw [← Real.sqrt_mul]; norm_num; linarith] at o
        rw [Real.sqrt_eq_iff_eq_sq] at o
        norm_num at o
        norm_num
        norm_num
        