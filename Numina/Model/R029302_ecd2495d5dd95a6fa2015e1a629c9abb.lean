import Mathlib

theorem number_theory_199143 : ¬ (∃ s : Fin 33 → ℤ, (∀ i, s i = 1 ∨ s i = -1) ∧ Even (∑ i, s i * (i + 25))) := by 
  rintro ⟨s, hs1, heven⟩
  have h3 : (∑ i : Fin 33, s i * ((i : Fin 33).val + 25) ) % 2 = 1 := by
    have h4 : ∀ i : Fin 33, (s i * ((i : Fin 33).val + 25) : ℤ) % 2 = 
      if (i.val : ℕ) % 2 = 0 then (1 : ℤ) else (0 : ℤ) := by
      intro i 
      have h10 : s i = 1 ∨ s i = -1 := hs1 i
      by_cases h11 : (i.val : ℕ) % 2 = 0
      · -- If `i.val` is even, then `i.val + 25` is odd.
        by_cases h12 : s i = 1
        · -- If s i = 1
          have h5 : ((i : Fin 33).val + 25 : ℤ) % 2 = 1 := by
            have h7' : (i.val : ℤ) % 2 = 0 := by 
              exact_mod_cast h11 
            omega 
          simp [h12, Int.mul_emod, h5, h11]
        · -- s i = -1 
          have h13 : s i = -1 := by 
            omega 
          have h5 : ((i : Fin 33).val + 25 : ℤ) % 2 = 1 := by 
            have h7' : (i.val : ℤ) % 2 = 0 := by 
              exact_mod_cast h11 
            omega 
          simp [h13, Int.mul_emod, h5, h11]
          <;> omega
      · -- If `i.val` is odd, then `i.val + 25` is even.
        have h11' : (i.val : ℕ) % 2 = 1 := by 
          omega 
        by_cases h12 : s i = 1
        · -- s i = 1 
          have h5 : ((i : Fin 33).val + 25 : ℤ) % 2 = 0 := by 
            have h7' : (i.val : ℤ) % 2 = 1 := by 
              exact_mod_cast h11' 
            omega 
          simp [h12, Int.mul_emod, h5, h11']
          <;> omega
        · -- s i = -1 
          have h13 : s i = -1 := by 
            omega 
          have h5 : ((i : Fin 33).val + 25 : ℤ) % 2 = 0 := by 
            have h7' : (i.val : ℤ) % 2 = 1 := by 
              exact_mod_cast h11' 
            omega 
          simp [h13, Int.mul_emod, h5, h11']
          <;> omega
    have h5 : (∑ i : Fin 33, (s i * ((i : Fin 33).val + 25) : ℤ) ) % 2 = 1 := by
      have h6 : (∑ i : Fin 33, (s i * ((i : Fin 33).val + 25) : ℤ) ) % 2 =
        (∑ i : Fin 33, (s i * ((i : Fin 33).val + 25) : ℤ) % 2 ) % 2 := by 
        simp [Finset.sum_int_mod]
      rw [h6]
      have h7 : ∑ i : Fin 33, (s i * ((i : Fin 33).val + 25) : ℤ) % 2 = 17 := by 
        simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, h4]
        <;> native_decide
      simp [h7]
      <;> omega
    exact_mod_cast h5
  -- The sum must be even by h1 and odd by h5, hence a contradiction
  have h8 : (∑ i : Fin 33, s i * ((i : Fin 33).val + 25) : ℤ) % 2 = 0 := by
    obtain ⟨k, hk⟩ := heven 
    omega 
  omega