import Mathlib

theorem number_theory_123012 (a : ℤ) : 35 ∣ (a^3 - 1) ↔ a ≡ 1 [ZMOD 35] ∨ a ≡ 11 [ZMOD 35] ∨ a ≡ 16 [ZMOD 35] := by 
  constructor
  · -- Forward: if 35 divides a^3 - 1 then these congruences
    intro h
    have h1 : a ^ 3 % 35 = 1 := by
      omega 
    have h1a : a ^ 3 % 5 = 1 := by
      omega 
    have h1b : a % 5 = 0 ∨ a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by
      omega 
    -- Solving for a modulo 5
    -- a^3 ≡ 1 [mod 5] implies a ≡ 1 [mod 5]
    have h3 : a % 5 = 1 := by
      rcases h1b with (h | h | h | h | h) <;> 
        simp [h, pow_succ, Int.add_emod, Int.mul_emod] at h1a ⊢ 
        <;> omega 
    -- Solving for a modulo 7
    have h2a : a ^ 3 % 7 = 1 := by
      omega
    have h2b : a % 7 = 0 ∨ a % 7 = 1 ∨ a % 7 = 2 ∨ a % 7 = 3 ∨ a % 7 = 4 ∨ a % 7 = 5 ∨ a % 7 = 6 := by
      omega 
    -- Solving a^3 ≡ 1 [mod 7] gives a ≡ 1, 2, 4 [mod 7]
    have h5 : a % 7 = 1 ∨ a % 7 = 2 ∨ a % 7 = 4 := by 
      rcases h2b with (h | h | h | h | h | h | h) <;> 
        simp [h, pow_succ, Int.add_emod, Int.mul_emod] at h2a ⊢ 
        <;> omega 
    -- Break into cases 
    rcases h5 with (h7 | h7 | h7)
    · 
      -- a ≡ 1 mod 7 
      have h6 : a % 35 = 1 := by 
        omega 
      have h7 : a ≡ 1 [ZMOD 35] := by 
        simp [Int.ModEq] at *
        omega 
      left 
      exact h7 
    · 
      -- a ≡ 2 mod 7 
      have h8 : a % 35 = 16 := by
        omega 
      have h9 : a ≡ 16 [ZMOD 35] := by 
        simp [Int.ModEq] at *
        omega 
      right 
      right 
      exact h9 
    · 
      -- a ≡ 4 mod 7 
      have h10 : a % 35 = 11 := by
        omega 
      have h11 : a ≡ 11 [ZMOD 35] := by 
        simp [Int.ModEq] at *
        omega 
      right 
      left 
      exact h11 
  · -- Backward: these congruences imply 35 divides a^3 - 1
    rintro (h | h | h)
    · -- a ≡ 1 [ZMOD 35]
      have h1 : a % 35 = 1 := by 
        simp [Int.ModEq] at h 
        omega 
      have h2 : a^3 % 35 = 1 := by 
        simp [h1, pow_succ, Int.add_emod, Int.mul_emod]
      omega 
    · -- a ≡ 11 [ZMOD 35]
      have h1 : a % 35 = 11 := by 
        simp [Int.ModEq] at h 
        omega 
      have h2 : a^3 % 35 = 1 := by 
        simp [h1, pow_succ, Int.add_emod, Int.mul_emod]
      omega 
    · -- a ≡ 16 [ZMOD 35]
      have h1 : a % 35 = 16 := by 
        simp [Int.ModEq] at h 
        omega 
      have h2 : a^3 % 35 = 1 := by 
        simp [h1, pow_succ, Int.add_emod, Int.mul_emod]
      omega