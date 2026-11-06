import Mathlib

theorem algebra_7448
    {a b c k : ℝ}
    (ha : ¬∃ x : ℝ, a * x ^ 2 + b * x + c = 0)
    : ¬∃ x : ℝ, a * x ^ 2 + (b - 2 * a * k) * x + (a * k ^ 2 - b * k + c) = 0 := by
  rintro ⟨y, hy⟩
  have h_eq : a * (y - k) ^ 2 + b * (y - k) + c = 0 := by 
    nlinarith [hy]
  have h_contra : ∃ x : ℝ, a * x ^ 2 + b * x + c = 0 := by 
    refine' ⟨y - k, ?_⟩
    linarith
  contradiction