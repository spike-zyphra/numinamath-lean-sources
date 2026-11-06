import Mathlib

theorem algebra_10623 : {m : ℝ | ∃ x y, x ≠ y ∧ x^2 + m * x + 4 = 0 ∧ y^2 + m * y + 4 = 0} = Set.Iio (-4) ∪ Set.Ioi 4 := by
  ext m
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
  constructor
  · -- Assume m is in the left side set, prove it's in the right side set
    rintro ⟨x, y, hxy, hx, hy⟩
    have h3 : (x - y) * (x + y + m) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h3) with h4 h5
    · -- Case x - y = 0
      exfalso
      apply hxy
      linarith
    · -- Case x + y + m = 0
      have h6 : (x - y) ^ 2 > 0 := by
        apply sq_pos_of_ne_zero
        intro h
        apply hxy
        linarith
      have h7 : (x - y) ^ 2 = m^2 - 16 := by
        have h8 : x + y = -m := by
          linarith
        have h9 : x * y = 4 := by
          nlinarith [sq_pos_of_ne_zero (show (x - y) ≠ 0 by
            intro h'
            apply hxy
            linarith
          ), sq_nonneg (x - y), sq_nonneg (x + y + m)]
        calc
          (x - y) ^ 2 = (x + y) ^ 2 - 4 * (x * y) := by
            linarith [show (x * y : ℝ) = x * y by rfl]
          _ = (-m) ^ 2 - 4 * (4) := by rw [h8, h9]
          _ = m ^ 2 - 16 := by
            ring
      have h8 : m^2 > 16 := by
        nlinarith [h7, h6]
      by_cases h9 : m > 0
      · -- If m > 0, then m > 4
        have h10 : m > 4 := by
          nlinarith [h8, h9]
        right
        linarith
      · -- If m ≤ 0, then m < -4
        have h11 : m < -4 := by
          nlinarith [h8, show m ≤ 0 by linarith]
        left
        linarith
  · -- Assume m is in the right side set, prove it's in the left side set
    rintro (hm | hm)
    · -- Case m < -4
      have h1 : m ^ 2 > 16 := by nlinarith
      use (-m + Real.sqrt (m ^ 2 - 16)) / 2, (-m - Real.sqrt (m ^ 2 - 16)) / 2
      constructor
      · -- Show the two roots are distinct
        by_contra h
        have h3 : Real.sqrt (m ^ 2 - 16) = 0 := by nlinarith [h]
        have h4 : m ^ 2 - 16 = 0 := by
          rw [Real.sqrt_eq_zero (by nlinarith)] at h3
          linarith
        nlinarith
      constructor
      · -- Show the first root satisfies the quadratic
        nlinarith [Real.sqrt_nonneg (m ^ 2 - 16), Real.sq_sqrt (show m ^ 2 - 16 ≥ 0 by nlinarith)]
      · -- Show the second root satisfies the quadratic
        nlinarith [Real.sqrt_nonneg (m ^ 2 - 16), Real.sq_sqrt (show m ^ 2 - 16 ≥ 0 by nlinarith)]
    · -- Case m > 4
      have h1 : m ^ 2 > 16 := by nlinarith
      use (-m + Real.sqrt (m ^ 2 - 16)) / 2, (-m - Real.sqrt (m ^ 2 - 16)) / 2
      constructor
      · -- Show the two roots are distinct
        by_contra h
        have h3 : Real.sqrt (m ^ 2 - 16) = 0 := by nlinarith [h]
        have h4 : m ^ 2 - 16 = 0 := by
          rw [Real.sqrt_eq_zero (by nlinarith)] at h3
          linarith
        nlinarith
      constructor
      · -- Show the first root satisfies the quadratic
        nlinarith [Real.sqrt_nonneg (m ^ 2 - 16), Real.sq_sqrt (show m ^ 2 - 16 ≥ 0 by nlinarith)]
      · -- Show the second root satisfies the quadratic
        nlinarith [Real.sqrt_nonneg (m ^ 2 - 16), Real.sq_sqrt (show m ^ 2 - 16 ≥ 0 by nlinarith)]