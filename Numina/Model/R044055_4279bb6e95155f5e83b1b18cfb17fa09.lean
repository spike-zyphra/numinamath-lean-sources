import Mathlib

theorem number_theory_183408 (a b c : ℕ) (h : a + b + c ≡ 0 [ZMOD 6]) :
    a^3 + b^3 + c^3 ≡ 0 [ZMOD 6] := by
  have h1 : (a : ℤ) + (b : ℤ) + (c : ℤ) ≡ 0 [ZMOD 6] := by 
    exact_mod_cast h
  -- Now we prove that for each variable, x^3 ≡ x (mod 6)
  have h11 : (a : ℤ) % 6 = 0 ∨ (a : ℤ) % 6 = 1 ∨ (a : ℤ) % 6 = 2 ∨ (a : ℤ) % 6 = 3 ∨ (a : ℤ) % 6 = 4 ∨ (a : ℤ) % 6 = 5 := by 
    omega
  have h12 : (b : ℤ) % 6 = 0 ∨ (b : ℤ) % 6 = 1 ∨ (b : ℤ) % 6 = 2 ∨ (b : ℤ) % 6 = 3 ∨ (b : ℤ) % 6 = 4 ∨ (b : ℤ) % 6 = 5 := by 
    omega
  have h13 : (c : ℤ) % 6 = 0 ∨ (c : ℤ) % 6 = 1 ∨ (c : ℤ) % 6 = 2 ∨ (c : ℤ) % 6 = 3 ∨ (c : ℤ) % 6 = 4 ∨ (c : ℤ) % 6 = 5 := by 
    omega
  have h2 : (a^3 : ℤ) % 6 = (a : ℤ) % 6 := by 
    have h14 : (a : ℤ) % 6 = 0 ∨ (a : ℤ) % 6 = 1 ∨ (a : ℤ) % 6 = 2 ∨ (a : ℤ) % 6 = 3 ∨ (a : ℤ) % 6 = 4 ∨ (a : ℤ) % 6 = 5 := by 
      omega
    rcases h14 with (h14 | h14 | h14 | h14 | h14 | h14) <;> simp [h14, pow_succ, Int.add_emod, Int.mul_emod]
  -- For b 
  have h3 : (b^3 : ℤ) % 6 = (b : ℤ) % 6 := by 
    have h15 : (b : ℤ) % 6 = 0 ∨ (b : ℤ) % 6 = 1 ∨ (b : ℤ) % 6 = 2 ∨ (b : ℤ) % 6 = 3 ∨ (b : ℤ) % 6 = 4 ∨ (b : ℤ) % 6 = 5 := by 
      omega
    rcases h15 with (h15 | h15 | h15 | h15 | h15 | h15) <;> simp [h15, pow_succ, Int.add_emod, Int.mul_emod]
  -- For c 
  have h4 : (c^3 : ℤ) % 6 = (c : ℤ) % 6 := by 
    have h16 : (c : ℤ) % 6 = 0 ∨ (c : ℤ) % 6 = 1 ∨ (c : ℤ) % 6 = 2 ∨ (c : ℤ) % 6 = 3 ∨ (c : ℤ) % 6 = 4 ∨ (c : ℤ) % 6 = 5 := by 
      omega
    rcases h16 with (h16 | h16 | h16 | h16 | h16 | h16) <;> simp [h16, pow_succ, Int.add_emod, Int.mul_emod]
  -- Now show that a^3 + b^3 + c^3 ≡ a + b + c (mod 6)
  have h5 : (a^3 + b^3 + c^3 : ℤ) ≡ (a + b + c : ℤ) [ZMOD 6] := by
    simp [Int.ModEq, Int.add_emod, Int.mul_emod, h2, h3, h4]
  -- We know from the hypothesis (h1) that a + b + c ≡ 0 [ZMOD 6]
  -- So, we can use transitivity to show a^3 + b^3 + c^3 ≡ 0 [ZMOD 6]
  exact Int.ModEq.trans h5 h1