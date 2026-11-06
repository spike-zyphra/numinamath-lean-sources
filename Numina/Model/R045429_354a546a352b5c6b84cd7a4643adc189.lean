import Mathlib

theorem algebra_29262 {x y : ℕ} (hx : x > 0) (hy : y > 0)
    (hxy : |(x : ℤ) - y| = 3) (hsum : x^2 + y^2 = 117) :
    max x y = 9 := by
  have h1 : (x : ℤ) - y = 3 ∨ (y - (x : ℤ) = 3) := by
    cases' eq_or_eq_neg_of_abs_eq hxy with h h
    · left
      linarith
    · right
      linarith

  cases h1 with
  | inl h2 =>
    have h2' : (x : ℤ) = y + 3 := by linarith
    have h3 : x = y + 3 := by
      norm_cast at h2' ⊢
    rw [h3] at hsum
    have : y ≤ 10 := by
      nlinarith
    interval_cases y <;> omega
  | inr h2 =>
    have h2' : (y : ℤ) = (x : ℤ) + 3 := by linarith
    have h3 : y = x + 3 := by
      norm_cast at h2' ⊢
    rw [h3] at hsum
    have : x ≤ 10 := by
      nlinarith
    interval_cases x <;> omega