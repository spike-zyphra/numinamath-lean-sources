import Mathlib

theorem number_theory_135087 (n : ℕ) :
    Even ((3^n) % 100 / 10) := by
  have h1 : ∀ n : ℕ, (3^n) % 20 = 1 ∨ (3^n) % 20 = 3 ∨ (3^n) % 20 = 7 ∨ (3^n) % 20 = 9 := by
    intro n 
    induction n with 
    | zero =>
      norm_num
    | succ n ih =>
      simp [Nat.pow_succ, Nat.mul_mod] at ih ⊢ 
      omega
  have h6 : (3^n) % 100 = 1 ∨ (3^n) % 100 = 3 ∨ (3^n) % 100 = 7 ∨ (3^n) % 100 = 9 ∨ (3^n) % 100 = 21 ∨ (3^n) % 100 = 23 ∨ (3^n) % 100 = 27 ∨ (3^n) % 100 = 29 ∨ (3^n) % 100 = 41 ∨ (3^n) % 100 = 43 ∨ (3^n) % 100 = 47 ∨ (3^n) % 100 = 49 ∨ (3^n) % 100 = 61 ∨ (3^n) % 100 = 63 ∨ (3^n) % 100 = 67 ∨ (3^n) % 100 = 69 ∨ (3^n) % 100 = 81 ∨ (3^n) % 100 = 83 ∨ (3^n) % 100 = 87 ∨ (3^n) % 100 = 89 := by
    have h5 : (3^n) % 20 = 1 ∨ (3^n) % 20 = 3 ∨ (3^n) % 20 = 7 ∨ (3^n) % 20 = 9 := h1 n
    rcases h5 with (h | h | h | h)
    · 
      have : (3 ^ n) % 20 = 1 := h 
      have : (3 ^ n) % 100 = 1 ∨ (3 ^ n) % 100 = 21 ∨ (3 ^ n) % 100 = 41 ∨ (3 ^ n) % 100 = 61 ∨ (3 ^ n) % 100 = 81 := by
        have h8 : (3 ^ n) % 20 = 1 := h 
        omega
      tauto
    · 
      have : (3 ^ n) % 20 = 3 := h 
      have : (3 ^ n) % 100 = 3 ∨ (3 ^ n) % 100 = 23 ∨ (3 ^ n) % 100 = 43 ∨ (3 ^ n) % 100 = 63 ∨ (3 ^ n) % 100 = 83 := by
        have h8 : (3 ^ n) % 20 = 3 := h 
        omega
      tauto
    · 
      have : (3 ^ n) % 20 = 7 := h 
      have : (3 ^ n) % 100 = 7 ∨ (3 ^ n) % 100 = 27 ∨ (3 ^ n) % 100 = 47 ∨ (3 ^ n) % 100 = 67 ∨ (3 ^ n) % 100 = 87 := by
        have h8 : (3 ^ n) % 20 = 7 := h 
        omega
      tauto
    · 
      have : (3 ^ n) % 20 = 9 := h 
      have : (3 ^ n) % 100 = 9 ∨ (3 ^ n) % 100 = 29 ∨ (3 ^ n) % 100 = 49 ∨ (3 ^ n) % 100 = 69 ∨ (3 ^ n) % 100 = 89 := by
        have h8 : (3 ^ n) % 20 = 9 := h 
        omega
      tauto
  have h7 : ((3^n) % 100 / 10) % 2 = 0 := by
    rcases h6 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> 
      omega
  exact ⟨((3^n) % 100 / 10) / 2, by omega⟩