import Mathlib

theorem algebra_246024 (x y z : ℝ) (h₀ : x + y + z = 2) (h₁ : x * y + y * z + z * x = 1) :
    x ∈ Set.Icc 0 (4 / 3) ∧ y ∈ Set.Icc 0 (4 / 3) ∧ z ∈ Set.Icc 0 (4 / 3) := by
  constructor
  · -- Show that x ∈ [0, 4/3]
    constructor
    · -- We need to prove 0 ≤ x
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
    · -- We need to prove x ≤ 4/3
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  constructor
  · -- Show that y ∈ [0, 4/3]
    constructor
    · -- We need to prove 0 ≤ y
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
    · -- We need to prove y ≤ 4/3
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  · -- Show that z ∈ [0, 4/3]
    constructor
    · -- We need to prove 0 ≤ z
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
    · -- We need to prove z ≤ 4/3
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]