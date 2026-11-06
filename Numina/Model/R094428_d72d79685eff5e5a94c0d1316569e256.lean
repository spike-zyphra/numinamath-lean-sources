import Mathlib

theorem algebra_10459 {x y : ℕ} (hx : x > 0) (hy : y > 0)
    (hxy : |(x : ℤ) - y| = 12) (hxy' : x * y = 45) :
    x + y = 18 := by
  have h1 : (x : ℤ) - y = 12 ∨ (y : ℤ) - x = 12 := by
    cases eq_or_eq_neg_of_abs_eq hxy with
    | inl h =>
      left
      linarith
    | inr h =>
      right
      linarith
  cases h1 with
  | inl h2 =>
    have h3 : x = y + 12 := by
      omega
    rw [h3] at hxy'
    have h4 : y ≤ 45 := by
      nlinarith
    interval_cases y <;> omega
  | inr h2 =>
    have h3 : y = x + 12 := by
      omega
    rw [h3] at hxy'
    have h4 : x ≤ 45 := by
      nlinarith
    interval_cases x <;> omega