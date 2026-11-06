import Mathlib

theorem algebra_301354 {p q : ℝ} (hp : p ≠ 0 ∧ p ≠ 1)
    (x0 : ℝ) (hx0 : x0 = p * x0 + q) (a : ℕ → ℝ) (ha : ∀ n, a (n + 1) = p * a n + q) :
    ∀ n, a (n + 1) - x0 = p * (a n - x0) := by 
  intro n 
  calc
    a (n + 1) - x0 = (p * a n + q) - x0 := by rw [ha n]
    _ = p * (a n - x0) := by
      linarith [hx0]