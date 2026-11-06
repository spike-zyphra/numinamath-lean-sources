import Mathlib

def preccurlyeq (a b : ℕ) := b * 10 + a * 2

theorem algebra_188313 {x : ℕ} (hx : x = 130) : preccurlyeq 2011 x = 5322 := by
  rw [hx]
  all_goals rfl