import Mathlib

open Real

-- we prove a key lemma to simplify the equation --
lemma lemma_1 (a b: ℝ): |a - b| = abs (|a| - |b|) ↔ 0 ≤ a * b := by

  rw [← sq_eq_sq_iff_abs_eq_abs]
  ring_nf
  rw [sq_abs]
  rw [sq_abs]
  simp
  rw [← abs_mul]
  rw [← abs_eq_self]
  constructor
  .
    intro h
    symm
    exact h
  .
    intro h
    symm
    exact h


/-Find all solutions of the equation |sin2x - cosx| = ||sin2x| - |cosx|| on the interval (-2π; 2π] -/

theorem algebra_209116: {x : ℝ | x ∈ Set.Ioc (-2 * π) (2 * π) ∧
  |sin (2 * x) - cos x| = abs (|sin (2 * x)| - |cos x|)} =
  Set.Ioc (-2 * π) (- π) ∪ Set.Icc 0 π ∪ {-π / 2, 3 * π / 2, 2 * π} := by

  have d1:= Real.pi_gt_d2
  have d2:= Real.pi_lt_d2
  ext x
  simp only [Set.mem_setOf_eq]
  constructor

  -- the first direction
  .
    intro h
    rcases h with ⟨l, h⟩
    rw [lemma_1] at h
    rw [Real.sin_two_mul] at h
    by_cases g: cos x = 0

    -- case 1: cos x = 0
    .
      clear h
      rw [Real.cos_eq_zero_iff] at g
      simp at l
      obtain ⟨k, g⟩ := g
      have l1: k < 2 := by
        rify
        nlinarith
      have l2: -3 < k := by
        rify
        nlinarith
      interval_cases k
      all_goals norm_num at g; simp [g]
      .
        right
        right
        right
        left
        constructor
        .
          nlinarith
        .
          nlinarith
      .
        right
        right
        right
        right
        constructor
        .
          nlinarith
        .
          nlinarith

    -- case 2: cos x ≠ 0
    .
      rw [show 2 * sin x * cos x * cos x = (2 * (cos x) ^ 2) * sin x by ring] at h
      rw [mul_nonneg_iff_of_pos_left] at h
      by_contra! o
      absurd h
      simp
      clear g
      simp at o
      simp at l
      rcases o with ⟨l1, l2, l3, l4, l5⟩
      rcases l with ⟨r1, r2⟩
      simp [r1] at l4
      clear r1
      by_cases s: x < 0
      .
        apply Real.sin_neg_of_neg_of_neg_pi_lt
        exact s
        exact l4
      .
        simp at s
        simp [s] at l5
        clear s l4
        have j: 0 < -sin x := by
          rw [← Real.sin_sub_pi]
          apply Real.sin_pos_of_pos_of_lt_pi
          linarith
          by_contra! o
          replace o: x = 2 * π := by linarith
          simp [o] at l3
        linarith
      have j: 0 < (cos x) ^ 2 := by
        apply sq_pos_of_ne_zero
        exact g
      linarith

  -- the second direction
  .
    intro h
    rw [lemma_1]
    constructor
    .
      simp [h]
      simp at h
      constructor
      .
        rcases h with h | h | h | h | h
        all_goals nlinarith
      .
        rcases h with h | h | h | h | h
        all_goals nlinarith
    .
      rw [Real.sin_two_mul]
      rw [show 2 * sin x * cos x * cos x = (2 * (cos x) ^ 2) * sin x by ring]
      simp at h
      rcases h with h | h | h | h | h
      .
        have o: cos x = 0 := by
          rw [Real.cos_eq_zero_iff]
          use -1
          simp [h]
          ring
        simp [o]

      .
        have o: cos x = 0 := by
          rw [Real.cos_eq_zero_iff]
          use 1
          simp [h]
          ring
        simp [o]
      .
        have o: sin x = 0 := by
          rw [Real.sin_eq_zero_iff]
          use 2
          simp [h]
        simp [o]

      .
        apply mul_nonneg
        .
          have o: 0 ≤ (cos x) ^ 2 := by
            apply sq_nonneg
          linarith
        .
          rw [← Real.sin_add_two_pi]
          apply Real.sin_nonneg_of_nonneg_of_le_pi
          rcases h with ⟨l, r⟩
          .
            nlinarith
          .
            nlinarith
      .
        apply mul_nonneg
        .
          have o: 0 ≤ (cos x) ^ 2 := by
            apply sq_nonneg
          linarith
        .
          apply Real.sin_nonneg_of_nonneg_of_le_pi
          rcases h with ⟨l, r⟩
          .
            nlinarith
          .
            nlinarith
