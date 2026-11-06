import Mathlib

theorem number_theory_153810 (p : ℕ) (hp : p.Prime) :
    ¬(15 ∣ p^4 - 1) ↔ p = 3 ∨ p = 5 := by
  constructor
  · -- Assume ¬(15 ∣ p^4 - 1), we need to prove p = 3 ∨ p = 5
    intro h
    by_cases h1 : p ≤ 5
    · interval_cases p <;> norm_num at h ⊢ <;> tauto
    · -- p > 5
      have h2 : p > 5 := by linarith
      have h3 : p % 3 = 1 ∨ p % 3 = 2 := by
        by_contra h
        push_neg at h
        have h4 : p % 3 = 0 := by
          omega
        have h5 : ¬p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) (by omega) (by omega)
        contradiction
      have h4 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
        by_contra h
        push_neg at h
        have h6 : p % 5 = 0 := by
          omega
        have h60 : ¬p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p by omega) (by omega) (by omega)
        contradiction
      have h5 : (p ^ 4 : ℕ) % 3 = 1 := by
        rcases h3 with (h3 | h3)
        · -- p ≡ 1 [MOD 3]
          simp [Nat.pow_mod, h3]
        · -- p ≡ 2 [MOD 3]
          simp [Nat.pow_mod, h3]
      have h6 : (p ^ 4 : ℕ) % 5 = 1 := by
        rcases h4 with (h4 | h4 | h4 | h4)
        · -- p ≡ 1 [MOD 5]
          simp [Nat.pow_mod, h4]
        · -- p ≡ 2 [MOD 5]
          simp [Nat.pow_mod, h4]
        · -- p ≡ 3 [MOD 5]
          simp [Nat.pow_mod, h4]
        · -- p ≡ 4 [MOD 5]
          simp [Nat.pow_mod, h4]
      have h7 : 15 ∣ p ^ 4 - 1 := by
        have h8 : (p ^ 4 : ℕ) % 3 = 1 := h5
        have h9 : (p ^ 4 : ℕ) % 5 = 1 := h6
        have h10 : p ^ 4 % 3 = 1 := by
          omega
        have h11 : p ^ 4 % 5 = 1 := by
          omega
        have h77 : (p ^ 4 : ℕ) % 15 = 1 := by
          omega
        have h88 : (p ^ 4 - 1 : ℕ) % 15 = 0 := by
          omega
        omega
      contradiction
  · -- Assume p = 3 ∨ p = 5, prove ¬(15 ∣ p^4 - 1)
    rintro (h | h)
    · -- p = 3
      rw [h]
      norm_num
    · -- p = 5
      rw [h]
      norm_num