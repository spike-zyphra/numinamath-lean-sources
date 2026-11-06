import Mathlib

theorem number_theory_151580 :
    ¬∃ a d : ℕ, d = 1000 ∧ ∀ n ∈ Finset.range 3, Nat.Prime (a + d * n) := by 
  rintro ⟨a, d, h₁, h⟩
  have h2 : Nat.Prime (a + d * 0) := h 0 (Finset.mem_range.mpr (by norm_num))
  have h3 : Nat.Prime (a + d * 1) := h 1 (Finset.mem_range.mpr (by norm_num))
  have h4 : Nat.Prime (a + d * 2) := h 2 (Finset.mem_range.mpr (by norm_num))
  rw [h₁] at h2 h3 h4
  have h2' : Nat.Prime a := by 
    simpa using h2
  have h3' : Nat.Prime (a + 1000) := by 
    simpa using h3
  have h4' : Nat.Prime (a + 2000) := by 
    simpa using h4
  by_cases h5 : a % 3 = 0
  · -- case a % 3 = 0
    have h7 : a % 3 = 0 := h5
    by_cases h8 : a > 3
    · -- a > 3, and a divisible by 3
      have h8 : a % 3 = 0 := h5
      have h9 : ¬ Nat.Prime a := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ a by 
          omega 
        ) (by omega) (by omega)
      contradiction
    · -- a ≤ 3, and a divisible by 3
      have h11 : a = 0 ∨ a = 3 := by 
        omega
      rcases h11 with (h11 | h11)
      · -- case a = 0
        rw [h11] at h2'
        norm_num at h2'
      · -- case a = 3
        rw [h11] at h3'
        norm_num at h3'
  · -- case a % 3 ≠ 0
    have h5' : a % 3 = 1 ∨ a % 3 = 2 := by
      omega
    rcases h5' with (h5' | h5')
    · -- case a % 3 = 1
      have h8 : (a + 2000) % 3 = 0 := by 
        omega
      have h9 : ¬ Nat.Prime (a + 2000) := by 
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (a + 2000) by 
          omega 
        ) (by omega) (by omega)
      contradiction
    · -- case a % 3 = 2
      have h8 : (a + 1000) % 3 = 0 := by 
        omega
      have h9 : ¬ Nat.Prime (a + 1000) := by 
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (a + 1000) by 
          omega 
        ) (by omega) (by omega)
      contradiction