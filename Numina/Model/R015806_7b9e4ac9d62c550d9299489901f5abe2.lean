import Mathlib

theorem number_theory_193580 (n : ℕ) (h : ¬ 17 ∣ n) :
    17 ∣ n^8 + 1 ∨ 17 ∣ n^8 - 1 := by 
  have h1 : n % 17 = n % 17 := by 
    omega
  have h2 : n % 17 > 0 := by 
    by_contra h2
    push_neg at h2
    have h3 : n % 17 = 0 := by
      omega
    have h4 : 17 ∣ n := by 
      exact Nat.dvd_of_mod_eq_zero h3
    contradiction
  have h3 : n % 17 = 1 ∨ n % 17 = 2 ∨ n % 17 = 3 ∨ n % 17 = 4 ∨ n % 17 = 5 ∨ n % 17 = 6 ∨ n % 17 = 7 ∨ n % 17 = 8 ∨ n % 17 = 9 ∨ n % 17 = 10 ∨ n % 17 = 11 ∨ n % 17 = 12 ∨ n % 17 = 13 ∨ n % 17 = 14 ∨ n % 17 = 15 ∨ n % 17 = 16 := by
    omega
  rcases h3 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h)
  · -- case n % 17 = 1
    have h4 : n ^ 8 % 17 = 1 ∨ n ^ 8 % 17 = 16 := by 
      have h5 : n ^ 8 % 17 = 1 := by
        simp [pow_succ, Nat.mul_mod, h]
      tauto
    rcases h4 with (h | h1)
    · -- case n ^ 8 % 17 = 1, prove 17 ∣ n^8 - 1
      have : 17 ∣ n^8 - 1 := by 
        omega
      right
      exact this
    · -- case n ^ 8 % 17 = 16, prove 17 ∣ n^8 + 1
      have : 17 ∣ n^8 + 1 := by 
        omega
      left
      exact this
  · -- case n % 17 = 2
    have h4 : n ^ 8 % 17 = 1 ∨ n ^ 8 % 17 = 16 := by 
      have h5 : n ^ 8 % 17 = 1 := by
        simp [pow_succ, Nat.mul_mod, h]
      tauto
    rcases h4 with (h | h1)
    · -- case n ^ 8 % 17 = 1, prove 17 ∣ n^8 - 1
      have : 17 ∣ n^8 - 1 := by 
        omega
      right
      exact this
    · -- case n ^ 8 % 17 = 16, prove 17 ∣ n^8 + 1
      have : 17 ∣ n^8 + 1 := by 
        omega
      left
      exact this
  · -- case n % 17 = 3
    have h4 : n ^ 8 % 17 = 1 ∨ n ^ 8 % 17 = 16 := by 
      have h5 : n ^ 8 % 17 = 16 := by
        simp [pow_succ, Nat.mul_mod, h]
      tauto
    rcases h4 with (h | h1)
    · -- case n ^ 8 % 17 = 1, prove 17 ∣ n^8 - 1
      have : 17 ∣ n^8 - 1 := by 
        omega
      right
      exact this
    · -- case n ^ 8 % 17 = 16, prove 17 ∣ n^8 + 1
      have : 17 ∣ n^8 + 1 := by 
        omega
      left
      exact this
  · -- case n % 17 = 4
    have h4 : n ^ 8 % 17 = 1 ∨ n ^ 8 % 17 = 16 := by 
      have h5 : n ^ 8 % 17 = 1 := by
        simp [pow_succ, Nat.mul_mod, h]
      tauto
    rcases h4 with (h | h1)
    · -- case n ^ 8 % 17 = 1, prove 17 ∣ n^8 - 1
      have : 17 ∣ n^8 - 1 := by 
        omega
      right
      exact this
    · -- case n ^ 8 % 17 = 16, prove 17 ∣ n^8 + 1
      have : 17 ∣ n^8 + 1 := by 
        omega
      left
      exact this
  · -- case n % 17 = 5
    have h4 : n ^ 8 % 17 = 1 ∨ n ^ 8 % 17 = 16 := by 
      have h5 : n ^ 8 % 17 = 16 := by
        simp [pow_succ, Nat.mul_mod, h]
      tauto
    rcases h4 with (h | h1)
    · -- case n ^ 8 % 17 = 1, prove 17 ∣ n^8 - 1
      have : 17 ∣ n^8 - 1 := by 
        omega
      right
      exact this
    · -- case n ^ 8 % 17 = 16, prove 17 ∣ n^8 + 1
      have : 17 ∣ n^8 + 1 := by 
        omega
      left
      exact this
  · -- case n % 17 = 6
    have h4 : n ^ 8 % 17 = 1 ∨ n ^ 8 % 17 = 16 := by 
      have h5 : n ^ 8 % 17 = 16 := by
        simp [pow_succ, Nat.mul_mod, h]
      tauto
    rcases h4 with (h | h1)
    · -- case n ^ 8 % 17 = 1, prove 17 ∣ n^8 - 1
      have : 17 ∣ n^8 - 1 := by 
        omega
      right
      exact this
    · -- case n ^ 8 % 17 = 16, prove 17 ∣ n^8 + 1
      have : 17 ∣ n^8 + 1 := by 
        omega
      left
      exact this
  · -- case n % 17 = 7
    have h4 : n ^ 8 % 17 = 1 ∨ n ^ 8 % 17 = 16 := by 
      have h5 : n ^ 8 % 17 = 16 := by
        simp [pow_succ, Nat.mul_mod, h]
      tauto
    rcases h4 with (h | h1)
    · -- case n ^ 8 % 17 = 1, prove 17 ∣ n^8 - 1
      have : 17 ∣ n^8 - 1 := by 
        omega
      right
      exact this
    · -- case n ^ 8 % 17 = 16, prove 17 ∣ n^8 + 1
      have : 17 ∣ n^8 + 1 := by 
        omega
      left
      exact this
  · -- case n % 17 = 8
    have h4 : n ^ 8 % 17 = 1 ∨ n ^ 8 % 17 = 16 := by 
      have h5 : n ^ 8 % 17 = 1 := by
        simp [pow_succ, Nat.mul_mod, h]
      tauto
    rcases h4 with (h | h1)
    · -- case n ^ 8 % 17 = 1, prove 17 ∣ n^8 - 1
      have : 17 ∣ n^8 - 1 := by 
        omega
      right
      exact this
    · -- case n ^ 8 % 17 = 16, prove 17 ∣ n^8 + 1
      have : 17 ∣ n^8 + 1 := by 
        omega
      left
      exact this
  · -- case n % 17 = 9
    have h4 : n ^ 8 % 17 = 1 ∨ n ^ 8 % 17 = 16 := by 
      have h5 : n ^ 8 % 17 = 1 := by
        simp [pow_succ, Nat.mul_mod, h]
      tauto
    rcases h4 with (h | h1)
    · -- case n ^ 8 % 17 = 1, prove 17 ∣ n^8 - 1
      have : 17 ∣ n^8 - 1 := by 
        omega
      right
      exact this
    · -- case n ^ 8 % 17 = 16, prove 17 ∣ n^8 + 1
      have : 17 ∣ n^8 + 1 := by 
        omega
      left
      exact this
  · -- case n % 17 = 10
    have h4 : n ^ 8 % 17 = 1 ∨ n ^ 8 % 17 = 16 := by 
      have h5 : n ^ 8 % 17 = 16 := by
        simp [pow_succ, Nat.mul_mod, h]
      tauto
    rcases h4 with (h | h1)
    · -- case n ^ 8 % 17 = 1, prove 17 ∣ n^8 - 1
      have : 17 ∣ n^8 - 1 := by 
        omega
      right
      exact this
    · -- case n ^ 8 % 17 = 16, prove 17 ∣ n^8 + 1
      have : 17 ∣ n^8 + 1 := by 
        omega
      left
      exact this
  · -- case n % 17 = 11
    have h4 : n ^ 8 % 17 = 1 ∨ n ^ 8 % 17 = 16 := by 
      have h5 : n ^ 8 % 17 = 16 := by
        simp [pow_succ, Nat.mul_mod, h]
      tauto
    rcases h4 with (h | h1)
    · -- case n ^ 8 % 17 = 1, prove 17 ∣ n^8 - 1
      have : 17 ∣ n^8 - 1 := by 
        omega
      right
      exact this
    · -- case n ^ 8 % 17 = 16, prove 17 ∣ n^8 + 1
      have : 17 ∣ n^8 + 1 := by 
        omega
      left
      exact this
  · -- case n % 17 = 12
    have h4 : n ^ 8 % 17 = 1 ∨ n ^ 8 % 17 = 16 := by 
      have h5 : n ^ 8 % 17 = 16 := by
        simp [pow_succ, Nat.mul_mod, h]
      tauto
    rcases h4 with (h | h1)
    · -- case n ^ 8 % 17 = 1, prove 17 ∣ n^8 - 1
      have : 17 ∣ n^8 - 1 := by 
        omega
      right
      exact this
    · -- case n ^ 8 % 17 = 16, prove 17 ∣ n^8 + 1
      have : 17 ∣ n^8 + 1 := by 
        omega
      left
      exact this
  · -- case n % 17 = 13
    have h4 : n ^ 8 % 17 = 1 ∨ n ^ 8 % 17 = 16 := by 
      have h5 : n ^ 8 % 17 = 1 := by
        simp [pow_succ, Nat.mul_mod, h]
      tauto
    rcases h4 with (h | h1)
    · -- case n ^ 8 % 17 = 1, prove 17 ∣ n^8 - 1
      have : 17 ∣ n^8 - 1 := by 
        omega
      right
      exact this
    · -- case n ^ 8 % 17 = 16, prove 17 ∣ n^8 + 1
      have : 17 ∣ n^8 + 1 := by 
        omega
      left
      exact this
  · -- case n % 17 = 14
    have h4 : n ^ 8 % 17 = 1 ∨ n ^ 8 % 17 = 16 := by 
      have h5 : n ^ 8 % 17 = 16 := by
        simp [pow_succ, Nat.mul_mod, h]
      tauto
    rcases h4 with (h | h1)
    · -- case n ^ 8 % 17 = 1, prove 17 ∣ n^8 - 1
      have : 17 ∣ n^8 - 1 := by 
        omega
      right
      exact this
    · -- case n ^ 8 % 17 = 16, prove 17 ∣ n^8 + 1
      have : 17 ∣ n^8 + 1 := by 
        omega
      left
      exact this
  · -- case n % 17 = 15
    have h4 : n ^ 8 % 17 = 1 ∨ n ^ 8 % 17 = 16 := by 
      have h5 : n ^ 8 % 17 = 1 := by
        simp [pow_succ, Nat.mul_mod, h]
      tauto
    rcases h4 with (h | h1)
    · -- case n ^ 8 % 17 = 1, prove 17 ∣ n^8 - 1
      have : 17 ∣ n^8 - 1 := by 
        omega
      right
      exact this
    · -- case n ^ 8 % 17 = 16, prove 17 ∣ n^8 + 1
      have : 17 ∣ n^8 + 1 := by 
        omega
      left
      exact this
  · -- case n % 17 = 16
    have h4 : n ^ 8 % 17 = 1 ∨ n ^ 8 % 17 = 16 := by 
      have h5 : n ^ 8 % 17 = 1 := by
        simp [pow_succ, Nat.mul_mod, h]
      tauto
    rcases h4 with (h | h1)
    · -- case n ^ 8 % 17 = 1, prove 17 ∣ n^8 - 1
      have : 17 ∣ n^8 - 1 := by 
        omega
      right
      exact this
    · -- case n ^ 8 % 17 = 16, prove 17 ∣ n^8 + 1
      have : 17 ∣ n^8 + 1 := by 
        omega
      left
      exact this