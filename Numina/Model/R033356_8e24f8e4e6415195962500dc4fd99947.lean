import Mathlib
theorem algebra_607158 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (x ^ 2 + x + 1) * (y ^ 2 + y + 1) ≥ 9 * x * y ∧ ((x ^ 2 + x + 1) * (y ^ 2 + y + 1) = 9 * x * y ↔ x = 1 ∧ y = 1):= by
  have h1 : x ^ 2 + x + 1 ≥ 3 * x := by
    nlinarith [sq_nonneg (x - 1)]

  have h2 : y ^ 2 + y + 1 ≥ 3 * y := by
    nlinarith [sq_nonneg (y - 1)]

  have h3 : (x ^ 2 + x + 1) * (y ^ 2 + y + 1) ≥ 9 * x * y := by
    nlinarith [h1, h2, mul_pos hx hy]

  have h4 : (x ^ 2 + x + 1) * (y ^ 2 + y + 1) = 9 * x * y ↔ x = 1 ∧ y = 1 := by
    constructor
    · -- Assume (x ^ 2 + x + 1) * (y ^ 2 + y + 1) = 9 * x * y
      intro h_eq

      have h1_eq : x ^ 2 + x + 1 = 3 * x := by
        nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), h_eq, mul_pos hx hy]

      have h2_eq : y ^ 2 + y + 1 = 3 * y := by
        nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), h_eq, mul_pos hx hy]

      constructor
      · -- Show x = 1
        nlinarith

      · -- Show y = 1
        nlinarith
    · -- Assume x = 1 ∧ y = 1
      rintro ⟨rfl, rfl⟩
      norm_num

  constructor
  · exact h3
  · exact h4