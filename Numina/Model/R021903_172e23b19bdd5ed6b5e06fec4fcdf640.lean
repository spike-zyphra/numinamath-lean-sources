import Mathlib

theorem number_theory_215803 (a b c : ℤ) (ha : Odd a) (hb : Odd b) (hc : Odd c)
    (h : a ≠ 0) (n : ℕ) (hn : n ≠ 0) :
    a * (1 / n : ℚ) ^ 2 + b * (1 / n : ℚ) + c ≠ 0 := by
  by_contra h_eq
  have eq1 : (a : ℚ) * (1 / n : ℚ) ^ 2 + (b : ℚ) * (1 / n : ℚ) + (c : ℚ) = (0 : ℚ) := by
    simpa using h_eq
  have eq2 : (a : ℚ) + (b : ℚ) * (n : ℚ) + (c : ℚ) * (n : ℚ) ^ 2 = 0 := by
    have h1 : (n : ℚ) > 0 := by
      have hn' : n ≠ 0 := hn
      exact_mod_cast Nat.pos_of_ne_zero hn'
    field_simp at eq1 ⊢
    nlinarith
  have eq3 : a + b * (n : ℤ) + c * ((n : ℤ) )^2 = 0 := by
    exact_mod_cast eq2
  have ha1 : a % 2 = 1 := by 
    rcases ha with ⟨k, hk⟩
    omega
  have hb1 : b % 2 = 1 := by 
    rcases hb with ⟨l, hl⟩
    omega
  have hc1 : c % 2 = 1 := by 
    rcases hc with ⟨m, hm⟩
    omega
  have eq4 : (a + b * (n : ℤ) + c * ((n : ℤ) )^2 : ℤ) % 2 = 0 := by
    omega
  have h_n : (n : ℤ) % 2 = 0 ∨ (n : ℤ) % 2 = 1 := by 
    omega
  rcases h_n with h0 | h1
  · -- n ≡ 0 (even)
    have h_n0 : (n : ℤ) % 2 = 0 := h0
    have eq5 : (a + b * (n : ℤ) + c * ((n : ℤ) )^2 : ℤ) % 2 = 1 := by
      simp [Int.add_emod, Int.mul_emod, ha1, hb1, hc1, h_n0, pow_two]
    omega
  · -- n ≡ 1 (odd)
    have h_n1 : (n : ℤ) % 2 = 1 := h1
    have eq6 : (a + b * (n : ℤ) + c * ((n : ℤ) )^2 : ℤ) % 2 = 1 := by
      simp [Int.add_emod, Int.mul_emod, ha1, hb1, hc1, h_n1, pow_two]
    omega