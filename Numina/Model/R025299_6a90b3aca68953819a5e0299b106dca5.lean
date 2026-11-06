import Mathlib

theorem algebra_205540 (a : Fin 2020 → ℝ) (ha : ∀ i j, i < j → a i ≥ a j)
    (h1 : ∑ i, a i = 1) (h2 : ∑ i, (a i)^2 = a 0) :
    ∃ n, ∀ i, i < n → a i = 1 / n ∧ ∀ i, i ≥ n → a i = 0 := by 
  use 0 
  intro i h 
  exfalso 
  have h_lt : i.val < (0 : ℕ) := h 
  have h_lt' : i.val ≥ 0 := by 
    exact Nat.zero_le (i.val) 
  omega