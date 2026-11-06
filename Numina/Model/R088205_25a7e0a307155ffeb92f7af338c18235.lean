import Mathlib

theorem number_theory_96260 (h m : ℕ) (h₀ : h < 12) (h₁ : m < 60) :
    (Nat.digits 10 (h * 100 + m)).sum ≤ 23 := by
  interval_cases h <;> interval_cases m <;> norm_num
  <;> try { native_decide }