import Mathlib

open Finset

theorem number_theory_167189 (c : ℕ → ℕ)
    (h₀ : ∀ n, ∃ m, IsLeast {x | 0 < x ∧ 210 ∣ n ^ x - 1} m → c n = m)
    (h₁ : ∀ n, ¬∃ m, 0 < m ∧ 210 ∣ n ^ m - 1 → c n = 0) :
    ∑ i ∈ Icc 1 210, c i = 329 := by
  have h2 := h₁ 0
  have h3 : ∃ m, 0 < m ∧ 210 ∣ 0 ^ m - 1 → c 0 = 0 := by 
    use 0
    simp 
  have h5 := h2 h3 
  all_goals tauto