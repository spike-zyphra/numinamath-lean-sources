import Mathlib

theorem number_theory_256348 (n : ℕ) (hn : 0 < n) (a : Fin n → ℕ)
    (hsum : ∑ i : Fin n, a i ≡ 0 [ZMOD 30]) :
    ∑ i : Fin n, (a i)^5 ≡ 0 [ZMOD 30] := by
  have h1 (i : Fin n) : (a i : ℤ) ^ 5 % 30 = (a i : ℤ) % 30 := by
    have h1 : (a i : ℤ) ^ 5 % 2 = (a i : ℤ) % 2 := by 
      have h2 : (a i : ℤ) % 2 = 0 ∨ (a i : ℤ) % 2 = 1 := by 
        omega
      rcases h2 with (h | h)
      · 
        simp [h, pow_succ, Int.add_emod, Int.mul_emod]
      · 
        simp [h, pow_succ, Int.add_emod, Int.mul_emod]
    have h2 : (a i : ℤ) ^ 5 % 3 = (a i : ℤ) % 3 := by 
      have h3 : (a i : ℤ) % 3 = 0 ∨ (a i : ℤ) % 3 = 1 ∨ (a i : ℤ) % 3 = 2 := by 
        omega
      rcases h3 with (h | h | h)
      · 
        simp [h, pow_succ, Int.add_emod, Int.mul_emod]
      · 
        simp [h, pow_succ, Int.add_emod, Int.mul_emod]
      · 
        simp [h, pow_succ, Int.add_emod, Int.mul_emod]
    have h3 : (a i : ℤ) ^ 5 % 5 = (a i : ℤ) % 5 := by 
      have h4 : (a i : ℤ) % 5 = 0 ∨ (a i : ℤ) % 5 = 1 ∨ (a i : ℤ) % 5 = 2 ∨ (a i : ℤ) % 5 = 3 ∨ (a i : ℤ) % 5 = 4 := by 
        omega
      rcases h4 with (h | h | h | h | h)
      · 
        simp [h, pow_succ, Int.add_emod, Int.mul_emod]
      · 
        simp [h, pow_succ, Int.add_emod, Int.mul_emod]
      · 
        simp [h, pow_succ, Int.add_emod, Int.mul_emod]
      · 
        simp [h, pow_succ, Int.add_emod, Int.mul_emod]
      · 
        simp [h, pow_succ, Int.add_emod, Int.mul_emod]
    omega 
  have eq1 : (∑ i : Fin n, (a i)^5 : ℤ) % 30 = (∑ i : Fin n, (a i) : ℤ) % 30 := by
    have h3 (i : Fin n) : ((a i) ^ 5 : ℤ) % 30 = (a i : ℤ) % 30 := by 
      apply h1 i
    simp [Finset.sum_int_mod, h3]
  have h2 : (∑ i : Fin n, (a i) : ℤ) % 30 = 0 := by
    have hsum1 : (∑ i : Fin n, (a i) : ℤ) ≡ (0 : ℤ) [ZMOD 30] := by 
      exact hsum 
    norm_num [Int.ModEq] at hsum1 ⊢ 
    omega 
  norm_num [Int.ModEq] at *
  omega 
  all_goals omega