import Mathlib

theorem number_theory_11046 (n : ℕ) (h₀ : Nat.Prime n) (h₁ : ∀ k, n ∣ k + (k + 1) + (k + 2)) :
    n = 3 := by
  have h2 := h₁ 0
  have h3 : n ∣ 3 := by
    norm_num at h2 ⊢
    all_goals exact h2
  have h4 : n ≤ 3 := by 
    apply Nat.le_of_dvd (by norm_num) h3
  interval_cases n <;> norm_num at *
  <;> try { tauto }
  <;> norm_num at h₀ <;> tauto