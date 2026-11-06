import Mathlib

theorem number_theory_125242 (n : ℕ) (h₀ : 1 ≤ n) (h₁ : n ≤ 999)
    (h₂ : n^2 = (Nat.digits 10 n).sum^3) :
    n = 1 ∨ n = 27 := by
  interval_cases n <;> norm_num at h₂ ⊢ <;> try { tauto }