import Mathlib

theorem number_theory_227687 (n : ℕ) (h₀ : n ≥ 100) (h₁ : n ≤ 999)
    (h₂ : n = 33 * (Nat.digits 10 n).sum) :
    9 ∣ n ∧ n = 594 := by 
  interval_cases n <;> norm_num at h₂ ⊢ <;> try { omega }
  <;> norm_num
  <;> omega