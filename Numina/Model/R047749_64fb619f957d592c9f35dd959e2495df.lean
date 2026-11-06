import Mathlib

theorem number_theory_70427 {A : ℕ} (hA : Even A) (hA' : ¬ 10 ∣ A) :
    A^20 ≡ 76 [MOD 100] := by
  have h1 : A % 2 = 0 := by 
    obtain ⟨k, hk⟩ := hA
    omega
  have h2 : A % 5 ≠ 0 := by
    by_contra h
    have h5 : 10 ∣ A := by 
      omega
    contradiction
  have h3 : A ^ 20 % 4 = 0 := by
    have h4 : A % 2 = 0 := h1
    have h5 : A % 4 = 0 ∨ A % 4 = 2 := by
      omega
    rcases h5 with (h | h)
    · 
      simp [Nat.pow_mod, h, Nat.mul_mod]
    · 
      simp [Nat.pow_mod, h, Nat.mul_mod]
  have h4 : A ^ 20 % 25 = 1 := by
    have h5 : A % 5 ≠ 0 := by assumption
    have h6 : A % 25 = 1 ∨ A % 25 = 2 ∨ A % 25 = 3 ∨ A % 25 = 4 ∨
            A % 25 = 6 ∨ A % 25 = 7 ∨ A % 25 = 8 ∨ A % 25 = 9 ∨
            A % 25 = 11 ∨ A % 25 = 12 ∨ A % 25 = 13 ∨ A % 25 = 14 ∨
            A % 25 = 16 ∨ A % 25 = 17 ∨ A % 25 = 18 ∨ A % 25 = 19 ∨
            A % 25 = 21 ∨ A % 25 = 22 ∨ A % 25 = 23 ∨ A % 25 = 24 := by
      omega
    rcases h6 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> 
      simp [Nat.pow_mod, h, Nat.mul_mod]
  norm_num [Nat.ModEq] at *
  have h5 : A ^ 20 % 4 = 0 := h3
  have h6 : A ^ 20 % 25 = 1 := h4
  omega