import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_153289 (x y z : ℝ) :
  x^2 + y^2 = 8 ∧ x^2 * y^2 - z^2 = 16 ∧ sin (x^2 - 2 * y) = z ↔
  (x = 2 ∧ y = 2 ∧ z = 0) ∨ (x = -2 ∧ y = 2 ∧ z = 0) := by
  constructor
  · -- Forward: if the equations hold, then the solutions are as given.
    intro h
    rcases h with ⟨h1, h2, h3⟩
    have h4 : z^2 = x^2 * y^2 - 16 := by linarith
    have h5 : -1 ≤ z := by
      have h6 : -1 ≤ sin (x^2 - 2 * y) := by
        apply neg_one_le_sin
      linarith [show sin (x^2 - 2 * y) = z by linarith]
    have h6 : z ≤ 1 := by
      have h7 : sin (x^2 - 2 * y) ≤ 1 := by
        apply sin_le_one
      linarith [show sin (x^2 - 2 * y) = z by linarith]
    have h7 : x^2 * y^2 = 16 := by
      nlinarith [sq_nonneg (x^2 - 4), sq_nonneg (y^2 - 4), sq_nonneg (x^2 * y^2 - 16), sq_nonneg (z), sq_nonneg (z * z), Real.sin_sq_add_cos_sq (x^2 - 2 * y)]
    have h8 : z = 0 := by
      nlinarith [sq_nonneg (x^2 * y^2 - 16), sq_nonneg (z), sq_nonneg (z - 0), pow_two_nonneg (x^2 * y^2 - 16), pow_two_nonneg (z * (x^2 * y^2 - 16)), h7, h4]
    have h8' : (x^2) = 4 := by
      nlinarith [sq_nonneg (x^2 - 4), sq_nonneg (y^2 - 4), sq_nonneg (x^2 * y^2 - 16), sq_nonneg (z), sq_nonneg (x * y), h1, h7, h8]
    have h8'' : (y^2) = 4 := by
      nlinarith [sq_nonneg (x^2 - 4), sq_nonneg (y^2 - 4), sq_nonneg (x^2 * y^2 - 16), sq_nonneg (z), sq_nonneg (x * y), h1, h7, h8]
    have hx1 : x = 2 ∨ x = -2 := by
      have h8'2 : x^2 - 4 = 0 := by nlinarith
      have hx3 : (x - 2) * (x + 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp hx3) with hx4 hx5
      · left; linarith
      · right
        nlinarith
    have hy2 : y = 2 ∨ y = -2 := by
      have h8''2 : y^2 - 4 = 0 := by nlinarith
      have hy3 : (y - 2) * (y + 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp hy3) with hy4 hy5
      · left; linarith
      · right
        nlinarith
    rcases hx1 with (hx1 | hx1)
    · rcases hy2 with (hy2 | hy2)
      · -- Case where x = 2 and y = 2
        have h9 : x^2 - 2 * y = 0 := by
          rw [hx1, hy2]
          norm_num
        have : z = 0 := h8
        left
        constructor
        · linarith
        constructor
        · linarith
        · linarith
      · -- Case where x = 2 and y = -2
        exfalso
        have h9 : x^2 - 2 * y = 8 := by
          rw [hx1, hy2]
          norm_num
        have h11 : sin (x ^ 2 - 2 * y) = z := h3
        rw [show x^2 - 2 * y = (8 : ℝ) by
          linarith
        ] at h11
        have h100 : sin (8 : ℝ) > 0 := by
          have h2pi : sin (8 : ℝ) = sin ((8 : ℝ) - 2 * Real.pi) := by
            have h1 : sin (8 : ℝ) = sin ((8 : ℝ) - 2 * Real.pi) := by
              rw [show (8 : ℝ) - 2 * Real.pi = (8 : ℝ) - 2 * Real.pi by ring_nf]
              have h5 : sin (8) = sin ((8) - 2 * Real.pi) := by
                rw [show (8 - 2 * Real.pi : ℝ) = (8 : ℝ) - 2 * (Real.pi : ℝ) by ring]
                rw [sin_sub_two_pi]
                all_goals ring_nf
              linarith [h5]
            linarith [h1]
          have h314 : (0 : ℝ) < (8 : ℝ) - 2 * Real.pi := by
            linarith [Real.pi_lt_31416]
          have h314' : (8 : ℝ) - 2 * Real.pi < Real.pi := by
            linarith [Real.pi_lt_31416, Real.pi_gt_31415]
          have h314'' : sin ((8 : ℝ) - 2 * Real.pi) > 0 := by
            apply sin_pos_of_pos_of_lt_pi
            all_goals linarith
          rw [h2pi]
          all_goals linarith
          <;> linarith
        have h101 : z > 0 := by
          linarith [h11, h100]
        linarith [h8, h101]
    · rcases hy2 with (hy2 | hy2)
      · -- Case where x = -2 and y = 2
        have h9 : x^2 - 2 * y = 0 := by
          rw [hx1, hy2]
          norm_num
        have : z = 0 := h8
        right
        constructor
        · linarith
        constructor
        · linarith
        · linarith
      · -- Case where x = -2 and y = -2
        exfalso
        have h9 : x^2 - 2 * y = 8 := by
          rw [hx1, hy2]
          norm_num
        have h11 : sin (x ^ 2 - 2 * y) = z := h3
        rw [show x^2 - 2 * y = (8 : ℝ) by
          linarith
        ] at h11
        have h100 : sin (8 : ℝ) > 0 := by
          have h2pi : sin (8 : ℝ) = sin ((8 : ℝ) - 2 * Real.pi) := by
            have h1 : sin (8 : ℝ) = sin ((8 : ℝ) - 2 * Real.pi) := by
              rw [show (8 : ℝ) - 2 * Real.pi = (8 : ℝ) - 2 * Real.pi by ring_nf]
              have h5 : sin (8) = sin ((8) - 2 * Real.pi) := by
                rw [show (8 - 2 * Real.pi : ℝ) = (8 : ℝ) - 2 * (Real.pi : ℝ) by ring]
                rw [sin_sub_two_pi]
                <;> ring_nf
                all_goals tauto
              linarith [h5]
            linarith [h1]
          have h314 : (0 : ℝ) < (8 : ℝ) - 2 * Real.pi := by
            linarith [Real.pi_lt_31416]
          have h314' : (8 : ℝ) - 2 * Real.pi < Real.pi := by
            linarith [Real.pi_lt_31416, Real.pi_gt_31415]
          have h314'' : sin ((8 : ℝ) - 2 * Real.pi) > 0 := by
            apply sin_pos_of_pos_of_lt_pi
            all_goals linarith
          rw [h2pi]
          all_goals linarith
          <;> linarith
        have h101 : z > 0 := by
          linarith [h11, h100]
        linarith [h8, h101]
  · -- Backward: the solutions satisfy the equations.
    rintro (h | h)
    · rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · -- Check x^2 + y^2 = 8
        norm_num
      constructor
      · -- Check x^2 * y^2 - z^2 = 16
        norm_num
      · -- Check sin (x^2 - 2 * y) = z
        norm_num [Real.sin_zero]
    · rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · -- Check x^2 + y^2 = 8
        norm_num
      constructor
      · -- Check x^2 * y^2 - z^2 = 16
        norm_num
      · -- Check sin (x^2 - 2 * y) = z
        norm_num [Real.sin_zero]
  all_goals tauto
  <;> try tauto <;> try nlinarith
  <;> try linarith [Real.pi_lt_31416, Real.pi_gt_31415]
  <;> try norm_num [Real.sin_zero]
  <;> try tauto
  <;> try native_decide