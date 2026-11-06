import Mathlib

theorem algebra_297084 {a b c : ℝ} (h : a^2 * (b - c) + b^2 * (c - a) + c^2 * (a - b) = 0) :
    a = b ∨ a = c ∨ b = c := by 
  have eq : (a - b) * (b - c) * (c - a) = 0 := by
    ring_nf at h ⊢
    linarith
  cases' (mul_eq_zero.mp eq) with h1 h2
  cases' (mul_eq_zero.mp h1) with h3 h4
  · -- Case $a - b = 0$, so $a = b$
    left
    linarith
  · -- Case $b - c = 0$, so $b = c$
    right
    right
    linarith
  · -- Case $c - a = 0$, so $a = c$
    right
    left
    linarith