import Mathlib

theorem algebra_88406 {x y : ℕ} (hx : x * 13 + y * 17 = 10000) (hy : x > 0) (hxy : y > 0)
    (hxy' : |(x : ℤ) - y| = 1) :
    (x * 13 + y * 17 + 40) = y * 13 + x * 17 := by
  have h1 : (x : ℤ) - (y : ℤ) = 1 ∨ (x : ℤ) - (y : ℤ) = -1 := by
    cases eq_or_eq_neg_of_abs_eq hxy' with
    | inl h =>
      left
      linarith
    | inr h =>
      right
      linarith
  cases h1 with
  | inl h1 =>
    have h2 : (x : ℤ) = (y : ℤ) + 1 := by linarith
    have h3 : x = y + 1 := by
      omega
    rw [show (x : ℕ) = y + 1 by omega] at hx
    omega
  | inr h1 =>
    have h4 : (x : ℤ) = (y : ℤ) - 1 := by linarith
    have h5 : y = x + 1 := by
      omega
    rw [show (y : ℕ) = x + 1 by omega] at hx
    omega