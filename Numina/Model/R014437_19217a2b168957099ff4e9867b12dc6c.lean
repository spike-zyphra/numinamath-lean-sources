import Mathlib

theorem number_theory_172454 (p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    7 * p * q^2 + p = q^3 + 43 * p^3 + 1 ↔ (p = 2 ∧ q = 7) := by
  constructor
  · -- Assume the equation, prove (p = 2 ∧ q = 7)
    intro h
    by_cases h1 : p > 2
    · -- p > 2.
      have h4 : p % 2 = 1 := by
        by_contra h2
        push_neg at h2
        have h2' : p % 2 = 0 := by
          omega
        have h8 : ¬p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
        contradiction
      -- Now p is odd.
      have h13 : (7 * p * q^2 + p : ℕ) % 2 = (q^3 + 43 * p^3 + 1 : ℕ) % 2 := by 
        omega
      have h18 : q % 2 = 0 ∨ q % 2 = 1 := by 
        omega
      rcases h18 with (h18 | h18)
      · -- If q is even
        have h100 : (7 * p * q^2 + p : ℕ) % 2 = 1 := by
          have h13 : p % 2 = 1 := by
            omega
          have h14 : q % 2 = 0 := by
            omega
          simp [Nat.add_mod, Nat.mul_mod, h13, h14, Nat.pow_mod, Nat.mul_mod]
        have h191 : (q^3 + 43 * p^3 + 1 : ℕ) % 2 = 0 := by
          have h13 : p % 2 = 1 := by
            omega
          have h14 : q % 2 = 0 := by
            omega
          simp [Nat.add_mod, Nat.mul_mod, h13, h14, Nat.pow_mod, Nat.mul_mod]
        omega
      · -- If q is odd
        have h100 : (7 * p * q^2 + p : ℕ) % 2 = 0 := by
          have h13 : p % 2 = 1 := by
            omega
          have h14 : q % 2 = 1 := by
            omega
          simp [Nat.add_mod, Nat.mul_mod, h13, h14, Nat.pow_mod, Nat.mul_mod]
        have h131 : (q^3 + 43 * p^3 + 1 : ℕ) % 2 = 1 := by
          have h13 : p % 2 = 1 := by
            omega
          have h14 : q % 2 = 1 := by
            omega
          simp [Nat.add_mod, Nat.mul_mod, h13, h14, Nat.pow_mod, Nat.mul_mod]
        omega
    · -- p ≤ 2.
      have h6 : p = 2 := by 
        interval_cases p <;> try tauto
      rw [h6] at h 
      have h7 : q = 7 := by
        have h14 : q ≤ 31 := by
          nlinarith [sq_nonneg (q - 7 : ℤ), sq_nonneg (q ^ 2 - 49 : ℤ),
            sq_nonneg (q : ℤ), sq_nonneg ((q : ℤ) - 28)]
        interval_cases q <;> try { norm_num at h ⊢; all_goals try tauto }
      constructor 
      · omega 
      · omega 
  · -- Assume (p = 2 ∧ q = 7), prove the equation.
    rintro ⟨rfl, rfl⟩
    norm_num