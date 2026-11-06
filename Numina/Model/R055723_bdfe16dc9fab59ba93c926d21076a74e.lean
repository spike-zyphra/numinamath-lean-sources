import Mathlib

theorem algebra_175475 (total : ℕ) (days : ℕ) (daily_prod : ℕ) (new_prod_rate : ℕ) :
    total = 1590 ∧
    days = 12 ∧
    daily_prod = 80 ∧
    new_prod_rate = 90 →
    (total - days * daily_prod) / new_prod_rate = 7 := by
  intro h
  rcases h with ⟨rfl, rfl, rfl, rfl⟩
  all_goals norm_num