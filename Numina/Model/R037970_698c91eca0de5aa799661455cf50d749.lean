import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_300592 :
  IsLeast {u | ∃ x y : ℝ, x ∈ Ioo (-2) 2 ∧ y ∈ Ioo (-2) 2 ∧ x * y = -1 ∧ u = 4 / (4 - x ^ 2) + 9 / (9 - y ^ 2)} (12 / 5) := by
  constructor
  · -- Show that 12/5 is in the set.
    use Real.sqrt (2 / 3)
    use - (Real.sqrt (3 / 2))
    constructor
    · -- Show that sqrt(2/3) ∈ (-2, 2)
      constructor
      · -- Show that sqrt(2/3) > -2
        have h1 : Real.sqrt (2 / 3) > 0 := by
          apply Real.sqrt_pos.mpr
          linarith
        linarith
      · -- Show that sqrt(2/3) < 2
        have h2 : Real.sqrt (2 / 3) < 2 := by
          rw [Real.sqrt_lt] <;> norm_num
        linarith
    constructor
    · -- Show that -sqrt(3/2) ∈ (-2, 2)
      constructor
      · -- Show that -sqrt(3/2) > -2
        have h3 : Real.sqrt (3 / 2) < 2 := by
          rw [Real.sqrt_lt] <;> norm_num
        linarith [show Real.sqrt (3 / 2) > 0 by apply Real.sqrt_pos.mpr; norm_num]
      · -- Show that -sqrt(3/2) < 2
        have h4 : Real.sqrt (3 / 2) > 0 := by
          apply Real.sqrt_pos.mpr
          norm_num
        linarith
    constructor
    · -- Show that sqrt(2/3) * (-sqrt(3/2)) = -1
      have h5 : Real.sqrt (2 / 3) * Real.sqrt (3 / 2) = 1 := by
        have h6 : Real.sqrt (2 / 3) * Real.sqrt (3 / 2) = Real.sqrt ((2 / 3) * (3 / 2)) := by
          rw [← Real.sqrt_mul (by norm_num)]
        rw [h6]
        norm_num [Real.sqrt_eq_iff_sq_eq]
        <;> norm_num
      nlinarith
    · -- Show that 12/5 = 4/(4 - (sqrt(2/3))^2) + 9/(9 - (-sqrt(3/2))^2)
      have h7 : (Real.sqrt (2 / 3) : ℝ) ^ 2 = (2 / 3: ℝ) := by
        rw [Real.sq_sqrt]
        norm_num
      have h8 : (- (Real.sqrt (3 / 2)) : ℝ) ^ 2 = (3 / 2: ℝ) := by
        have h9 : (Real.sqrt (3 / 2) : ℝ) ^ 2 = (3 / 2: ℝ) := by
          rw [Real.sq_sqrt]
          norm_num
        nlinarith
      rw [h7, h8]
      norm_num
  · -- Show that 12/5 is the least
    intro u hu
    rcases hu with ⟨x, y, hx, hy, hxy, heq⟩
    have hx1 : -2 < x := hx.1
    have hx2 : x < 2 := hx.2
    have hy1 : -2 < y := hy.1
    have hy2 : y < 2 := hy.2
    have h1 : 4 - x ^ 2 > 0 := by
      nlinarith [hxy, sq_nonneg (x ^ 2 - 1 / 9), sq_nonneg (y ^ 2 - 1 / 9), sq_pos_of_pos (show (4 - x ^ 2) > 0 by nlinarith), sq_pos_of_pos (show (9 - y ^ 2) > 0 by nlinarith)]
    have h2 : 9 - y ^ 2 > 0 := by
      nlinarith [hxy, sq_nonneg (x ^ 2 - 1 / 9), sq_nonneg (y ^ 2 - 1 / 9), sq_pos_of_pos (show (4 - x ^ 2) > 0 by nlinarith), sq_pos_of_pos (show (9 - y ^ 2) > 0 by nlinarith)]
    have h3 : x ^ 2 > (1 / 9 : ℝ) := by
      nlinarith [hxy, sq_nonneg (x ^ 2 - 1 / 9), sq_nonneg (y ^ 2 - 1 / 9), sq_pos_of_pos (show (4 - x ^ 2) > 0 by nlinarith), sq_pos_of_pos (show (9 - y ^ 2) > 0 by nlinarith)]
    have h4 : 9 * x ^ 2 - 1 > 0 := by
      nlinarith [hxy, sq_nonneg (x ^ 2 - 1 / 9), sq_nonneg (y ^ 2 - 1 / 9), sq_pos_of_pos (show (4 - x ^ 2) > 0 by nlinarith), sq_pos_of_pos (show (9 - y ^ 2) > 0 by nlinarith)]
    have h5 : 4 / (4 - x ^ 2) + 9 / (9 - y ^ 2) - 12 / 5 ≥ 0 := by
      have h6 : y ^ 2 = (1 / x ^ 2 : ℝ) := by
        field_simp [(show x ≠ 0 by nlinarith [hxy, sq_pos_of_pos (show (4 - x ^ 2) > 0 by nlinarith), sq_pos_of_pos (show (9 - y ^ 2) > 0 by nlinarith)])]
        <;> nlinarith [hxy, sq_nonneg (x * y + 1)]
      have h7 : 4 - x ^ 2 > 0 := h1
      have h8 : 9 - y ^ 2 > 0 := h2
      have h9 : (4 / (4 - x ^ 2) + 9 / (9 - y ^ 2) - 12 / 5) = (63 * (x ^ 2 - 2 / 3) ^ 2) / (5 * (4 - x ^ 2) * (9 * x ^ 2 - 1)) := by
        rw [show 9 - y ^ 2 = (9 * x ^ 2 - 1) / x ^ 2 by
          rw [h6]
          field_simp [(show x ≠ 0 by nlinarith [hxy, sq_pos_of_pos (show (4 - x ^ 2) > 0 by nlinarith), sq_pos_of_pos (show (9 - y ^ 2) > 0 by nlinarith)])]
          <;> nlinarith [hxy, sq_nonneg (x * y + 1)]
        ]
        field_simp [(show 4 - x ^ 2 ≠ 0 by nlinarith [h1]), (show 9 * x ^ 2 - 1 ≠ 0 by nlinarith [h4]), (show x ^ 2 ≠ 0 by nlinarith [show x ≠ 0 by nlinarith [hxy, sq_pos_of_pos (show (4 - x ^ 2) > 0 by nlinarith), sq_pos_of_pos (show (9 - y ^ 2) > 0 by nlinarith)]]), (show (9 * x ^ 2 - 1) > 0 by nlinarith [h4])]
        <;> ring_nf
      rw [h9]
      apply div_nonneg
      · -- Show that 63 * (x ^ 2 - 2 / 3) ^ 2 ≥ 0
        nlinarith [sq_nonneg (x ^ 2 - 2 / 3)]
      · -- Show that 5 * (4 - x ^ 2) * (9 * x ^ 2 - 1) ≥ 0
        positivity
    nlinarith [h5, heq]