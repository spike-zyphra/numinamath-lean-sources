import Mathlib

open Real Set

theorem algebra_2536 : {x : ℝ | ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ x = c / a + a / (b + c) + b / c} = {x | 2 < x} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Forward implication: if x is in the image of f, then x > 2.
    rintro ⟨a, b, c, ha, hb, hc, h_eq⟩
    have h1 : c / a + a / (b + c) + b / c > 2 := by
      have h1 : 0 < a * (b + c) * c := by
        positivity
      have h2 : c / a + a / (b + c) + b / c - 2 > 0 := by
        have h3 : c / a + a / (b + c) + b / c - 2 = (c^2 * (b + c) + a^2 * c + a * (b + c) * b - 2 * a * (b + c) * c) / (a * (b + c) * c) := by
          field_simp
          ring
        rw [h3]
        have h5 : c^2 * (b + c) + a^2 * c + a * (b + c) * b - 2 * a * (b + c) * c > 0 := by
          nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc,
            sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b - c),
            sq_nonneg (a - b), sq_nonneg (b + c - a), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
          ]
        have h6 : (c^2 * (b + c) + a^2 * c + a * (b + c) * b - 2 * a * (b + c) * c) / (a * (b + c) * c) > 0 := by
          apply div_pos
          linarith
          positivity
        linarith
      linarith
    linarith
  · -- Backward implication: if x > 2, then x is in the image of f.
    intro h
    have hx : 2 < x := by linarith
    have h3 : x ^ 2 > 4 := by nlinarith
    have h4 : x ^ 2 - 4 > 0 := by linarith
    have h5 : Real.sqrt (x ^ 2 - 4) > 0 := by apply Real.sqrt_pos.mpr; linarith
    have h6 : Real.sqrt (x ^ 2 - 4) ^ 2 = x ^ 2 - 4 := Real.sq_sqrt (by linarith)
    have h11 : x - 2 + Real.sqrt (x ^ 2 - 4) > 0 := by
      nlinarith [Real.sqrt_nonneg (x ^ 2 - 4), Real.sq_sqrt (show 0 ≤ x ^ 2 - 4 by nlinarith)]
    have h10 : (x - 2 + Real.sqrt (x ^ 2 - 4)) / 2 > 0 := by nlinarith
    use 1, (x - 2 + Real.sqrt (x ^ 2 - 4)) / 2, 1
    constructor
    · -- Show a > 0
      norm_num
    constructor
    · -- Show b > 0
      nlinarith
    constructor
    · -- Show c > 0
      norm_num
    · -- Show x = c / a + a / (b + c) + b / c
      field_simp [Real.sqrt_nonneg (x ^ 2 - 4), Real.sq_sqrt (show 0 ≤ x ^ 2 - 4 by nlinarith)]
      nlinarith [Real.sqrt_nonneg (x ^ 2 - 4), Real.sq_sqrt (show 0 ≤ x ^ 2 - 4 by nlinarith)]