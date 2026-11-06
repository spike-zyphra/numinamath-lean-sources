import Mathlib

theorem number_theory_183029 (n : ℕ) (h₀ : n > 0) (h₁ : n + 1 > 0) (h₂ : n + 2 > 0)
    (h₃ : Odd (n + (n + 1) + (n + 2))) :
    n * (n + 1) * (n + 2) ≡ 0 [ZMOD 24] := by 
  have h6 : (n : ℕ) % 2 = 0 := by
    have h7 : (n + (n + 1) + (n + 2) : ℕ) % 2 = 1 := by
      obtain ⟨k, hk⟩ := h₃
      omega
    have h_eq : n + (n + 1) + (n + 2) = 3 * (n + 1) := by
      omega
    rw [h_eq] at h7 
    omega
  have hs1 : (n * (n + 1) * (n + 2)) % 3 = 0 := by
    have h7 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by 
      omega
    rcases h7 with (h7 | h7 | h7)
    · -- n % 3 = 0
      simp [Nat.mul_mod, Nat.add_mod, h7]
      <;> omega 
    · -- n % 3 = 1
      simp [Nat.mul_mod, Nat.add_mod, h7]
      <;> omega 
    · -- n % 3 = 2
      simp [Nat.mul_mod, Nat.add_mod, h7]
      <;> omega 
  have hs2 : (n * (n + 1) * (n + 2)) % 8 = 0 := by
    have h8 : n % 2 = 0 := h6
    have h88 : n % 8 = 0 ∨ n % 8 = 2 ∨ n % 8 = 4 ∨ n % 8 = 6 := by 
      omega
    rcases h88 with (h | h | h | h)
    · -- n % 8 = 0
      simp [Nat.mul_mod, Nat.add_mod, h, Nat.mul_mod, Nat.add_mod]
      <;> omega
    · -- n % 8 = 2
      simp [Nat.mul_mod, Nat.add_mod, h, Nat.mul_mod, Nat.add_mod]
      <;> omega
    · -- n % 8 = 4
      simp [Nat.mul_mod, Nat.add_mod, h, Nat.mul_mod, Nat.add_mod]
      <;> omega
    · -- n % 8 = 6
      simp [Nat.mul_mod, Nat.add_mod, h, Nat.mul_mod, Nat.add_mod]
      <;> omega
  have h77 : ((n : ℕ) * ((n : ℕ) + 1) * ((n : ℕ) + 2)) % 24 = 0 := by
    omega
  norm_num [Int.ModEq]
  <;> try { 
    have h80 : ((n : ℤ) * ((n : ℤ) + 1) * ((n : ℤ) + 2)) % 24 = 0 := by
      exact_mod_cast h77
    omega
  }
  <;> try { tauto }
  <;> try { 
    omega 
  }
  all_goals try { tauto }
  all_goals try { nlinarith }
  all_goals try { tauto }
  all_goals try { nlinarith }
  all_goals try { tauto }
  all_goals try { nlinarith }
  all_goals try { tauto }