import Mathlib

theorem algebra_243134 {a b : ℕ} (ha : a < 20) (hb : b < 20)
    (h : ∃ x, a * x ^ 2 + b * x + 5 = 0 ∧ x = 5 * (a * (x / 5) ^ 2 + b * (x / 5) + 5)) :
    a * x ^ 2 + b * x + 5 = 0 ∧ x = 5 * (a * (x / 5) ^ 2 + b * (x / 5) + 5) ↔
    (a = 1 ∧ b = 6) ∨ (a = 4 ∧ b = 12) ∨ (a = 9 ∧ b = 18) := by
  rcases h with ⟨x, h1, h2⟩
  have h3 : a * x ^ 2 + b * x + 5 > 0 := by 
    have h4 : a * x ^ 2 ≥ 0 := by positivity
    have h5 : b * x ≥ 0 := by positivity
    have h6 : 5 > 0 := by norm_num
    omega
  omega