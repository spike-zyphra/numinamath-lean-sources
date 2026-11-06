import Mathlib

theorem number_theory_323862 (a d : ℕ) (h₀ : a > 0) (h₁ : d > 0)
    (h₂ : Nat.Prime a) (h₃ : Nat.Prime (a + d)) (h₄ : Nat.Prime (a + 2 * d))
    (h₅ : d = 8) :
    a = 3 := by
  subst h₅
  have h6 : a ≤ 37 := by
      -- Let's see, if such triplet can't be found below 37, so
    by_contra h
    push_neg at h
    have h7 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by 
      omega
    rcases h7 with (h7 | h7 | h7)
    · -- If a ≡ 0 [MOD 3]
      have h8 : ¬ Nat.Prime a := by 
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ a by omega)
        all_goals omega
      contradiction
    · -- If a ≡ 1 [MOD 3]
      have h8 : (a + 8) % 3 = 0 := by omega
      have h9 : 3 ∣ (a + 8) := by omega
      have h10 : ¬ Nat.Prime (a + 8) := by
        apply Nat.not_prime_of_dvd_of_lt h9
        all_goals omega
      contradiction
    · -- If a ≡ 2 [MOD 3]
      have h8 : (a + 16) % 3 = 0 := by 
        omega
      have h9 : 3 ∣ (a + 16) := by 
        omega
      have h10 : ¬ Nat.Prime (a + 16) := by
        apply Nat.not_prime_of_dvd_of_lt h9
        all_goals omega
      contradiction
  interval_cases a <;> norm_num at h₂ h₃ h₄ <;> all_goals { trivial }