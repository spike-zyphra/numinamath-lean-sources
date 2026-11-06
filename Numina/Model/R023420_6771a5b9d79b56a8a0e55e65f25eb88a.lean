import Mathlib

theorem algebra_3532 (p : ℕ) (hp : Nat.Prime p) :
    ∃ x1 x2 : ℤ, x1^2 - 2 * p * x1 + p^2 - 5 * p - 1 = 0 ∧
      x2^2 - 2 * p * x2 + p^2 - 5 * p - 1 = 0 ↔ p = 3 ∨ p = 7 := by
  by_cases h : p ≤ 7
  · -- p ≤ 7, check all primes less or equal to 7
    interval_cases p <;> try { 
      use 7, -1
      all_goals
      native_decide
    } <;> try { 
      use 13, 1
      all_goals
      native_decide 
    }
    <;> norm_num at hp ⊢ <;> norm_num
  · -- p > 7
    push_neg at h
    have h8 : p ≥ 8 := by linarith
    use 0, 0
    constructor
    · -- Assume the equations hold, prove p = 3 or p = 7
      intro h
      rcases h with ⟨h1, h2⟩
      norm_num at h1 h2
      have h10 : (p : ℤ) ^ 2 - 5 * (p : ℤ) - 1 = 0 := by
        nlinarith
      exfalso
      have h22 : (p : ℤ) ≥ (8 : ℤ) := by exact_mod_cast h8
      nlinarith
    · -- Assume p = 3 or p = 7, prove the equations
      rintro (h_eq3 | h_eq7)
      · -- Case p = 3, contradiction because p ≥ 8
        exfalso
        linarith
      · -- Case p = 7, contradiction because p ≥ 8
        exfalso
        linarith