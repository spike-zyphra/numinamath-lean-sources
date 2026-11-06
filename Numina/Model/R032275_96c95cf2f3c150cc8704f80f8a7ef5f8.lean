import Mathlib

theorem number_theory_231240 (n : ℕ) (hn : 0 < n) (a : Fin n → ℕ)
    (hsum : ∑ i : Fin n, a i ≡ 0 [ZMOD 30]) :
    ∑ i : Fin n, (a i)^5 ≡ 0 [ZMOD 30] := by 
  have h1 : ∀ x : ℕ, (x : ℤ) ^ 5 % 30 = (x : ℤ) % 30 := by
    intro x 
    have h1 : (x : ℤ) ^ 5 % 2 = (x : ℤ) % 2 := by
      have h2 : (x : ℤ) % 2 = 0 ∨ (x : ℤ) % 2 = 1 := by omega 
      rcases h2 with (h2 | h2) <;> simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
    have h2 : (x : ℤ) ^ 5 % 3 = (x : ℤ) % 3 := by
      have h2 : (x : ℤ) % 3 = 0 ∨ (x : ℤ) % 3 = 1 ∨ (x : ℤ) % 3 = 2 := by omega
      rcases h2 with (h2 | h2 | h2) <;> simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
    have h3 : (x : ℤ) ^ 5 % 5 = (x : ℤ) % 5 := by 
      have h2 : (x : ℤ) % 5 = 0 ∨ (x : ℤ) % 5 = 1 ∨ (x : ℤ) % 5 = 2 ∨ (x : ℤ) % 5 = 3 ∨ (x : ℤ) % 5 = 4 := by omega 
      rcases h2 with (h2 | h2 | h2 | h2 | h2) <;> simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
    omega

  have h2 : ∀ i : Fin n, ( (a i) ^ 5 : ℤ) % 30 = ( (a i) : ℤ) % 30 := by 
    intro i
    specialize h1 (a i)
    simpa using h1
  have h3 : ( ∑ i : Fin n, ( (a i)^5 : ℤ) ) % 30 = ( ∑ i : Fin n, ( (a i) : ℤ) ) % 30 := by
    have h4 : ∀ i : Fin n, ( (a i) ^ 5 : ℤ) % 30 = ( (a i) : ℤ) % 30 := h2 
    simp [Finset.sum_int_mod, h4]

  have h4 : ( (∑ i : Fin n, ( (a i)^5 : ℤ) ) ) % 30 = 0 := by
    have h5 : ( ( ∑ i : Fin n, ( (a i) : ℤ) ) ) % 30 = 0 := by 
      have h6 : ( ( ∑ i : Fin n, (a i) : ℕ ) : ℤ ) % 30 = 0 := by
        norm_num [Int.ModEq] at hsum ⊢
        exact_mod_cast hsum 
      have h7 : ( ( ∑ i : Fin n, ( (a i) : ℤ) ) ) = ( ( ∑ i : Fin n, (a i) : ℕ ) : ℤ ) := by
        simp [Finset.sum_congr]
      rw [h7]
      all_goals omega
    omega 
  norm_num [Int.ModEq] at h4 ⊢
  all_goals omega