import Mathlib

def p : ℕ → ℕ
| n => (Nat.digits 10 n).prod

theorem number_theory_265880 (n : ℕ) :
    n + p n = 70 ↔ n = 46 ∨ n = 70 := by 
  constructor
  · -- Forward implication: if n + p n = 70, then n = 46 or n = 70 
    intro h
    have h1 : n ≤ 70 := by
      have hpn : p n ≥ 0 := by positivity
      linarith
    interval_cases n <;> norm_num [p] at h ⊢ <;> tauto
  · -- Backward direction: if n = 46 or n = 70, then n + p n = 70 
    rintro (h | h)
    · -- Case n = 46
      rw [h]
      norm_num [p]
    · -- Case n = 70
      rw [h]
      norm_num [p]