import Mathlib

theorem number_theory_6862 {a : ℕ} (ha : Nat.gcd a 30 = 1) : 60 ∣ (a ^ 4 + 59) := by
  have h1 : a % 4 = 1 ∨ a % 4 = 3 := by
    have h2 : a % 2 = 1 := by
      have h3 : Nat.gcd a 30 = 1 := ha
      have h4 : ¬(2 ∣ a) := by
        by_contra h6
        have h7 : 2 ∣ a := h6
        have h8 : 2 ∣ a.gcd 30 := by
          apply Nat.dvd_gcd
          · exact h7
          · norm_num
        have h9 : a.gcd 30 = 1 := h3
        rw [h9] at h8
        omega
      have no : a % 2 ≠ 0 := by
        intro h
        have hdiv : 2 ∣ a := by 
          omega
        contradiction
      omega
    have h3 : a % 4 = 1 ∨ a % 4 = 3 := by
      omega
    exact h3
  have h2 : a ^ 4 % 4 = 1 := by
    rcases h1 with (h | h)
    · -- a ≡ 1 [MOD 4]
      simp [Nat.pow_mod, h]
    · -- a ≡ 3 [MOD 4]
      simp [Nat.pow_mod, h]
  have h3 : a ^ 4 % 3 = 1 := by
    have h1 : a % 3 = 1 ∨ a % 3 = 2 := by
      have h3 : a % 3 ≠ 0 := by
        intro h
        have h2 : 3 ∣ a := by 
          omega
        have h8 : 3 ∣ a.gcd 30 := by
          apply Nat.dvd_gcd
          · exact h2
          · norm_num
        have h9 : a.gcd 30 = 1 := ha
        rw [h9] at h8
        omega
      omega
    rcases h1 with (h | h)
    · -- a ≡ 1 [MOD 3]
      simp [Nat.pow_mod, h]
    · -- a ≡ 2 [MOD 3]
      simp [Nat.pow_mod, h]
  have h4 : a ^ 4 % 5 = 1 := by
    have h4 : a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by
      have h6 : a % 5 ≠ 0 := by
        intro h
        have h2 : 5 ∣ a := by 
          omega
        have h8 : 5 ∣ a.gcd 30 := by
          apply Nat.dvd_gcd
          · exact h2
          · norm_num
        have h9 : a.gcd 30 = 1 := ha
        rw [h9] at h8
        omega
      omega
    rcases h4 with (h | h | h | h)
    · -- a ≡ 1 [MOD 5]
      simp [Nat.pow_mod, h]
    · -- a ≡ 2 [MOD 5]
      simp [Nat.pow_mod, h]
    · -- a ≡ 3 [MOD 5]
      simp [Nat.pow_mod, h]
    · -- a ≡ 4 [MOD 5]
      simp [Nat.pow_mod, h]
  omega