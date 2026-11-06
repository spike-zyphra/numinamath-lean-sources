import Mathlib

theorem inequalities_222228 (n : ℕ) (a : Fin n → ℝ)
    (h₀ : ∀ i, 0 < a i) (h₁ : ∏ i, a i = 1) :
    ∏ i, (1 + a i) ≥ 2 ^ n := by

  have h2 : ∀ i, (1 + a i) ≥ 2 * Real.sqrt (a i) := by 
    intro i 
    have ha_i : 0 < a i := h₀ i 
    nlinarith [Real.sqrt_nonneg (a i), Real.sq_sqrt (show (0 : ℝ) ≤ a i by linarith), sq_nonneg (a i - 1)]

  have h3a : ∀ i, 0 < Real.sqrt (a i) := by 
    intro i 
    have ha_i_pos : 0 < a i := h₀ i 
    have h4 : Real.sqrt (a i) > 0 := by
      apply Real.sqrt_pos.mpr 
      linarith 
    linarith

  have h4a : ∀ i, (2 * Real.sqrt (a i) ) ≥ 0 := by
    intro i 
    have h5a : 0 < Real.sqrt (a i) := h3a i 
    nlinarith [Real.sqrt_nonneg (a i)]

  have h3 : ∏ i, (1 + a i) ≥ ∏ i, (2 * Real.sqrt (a i)) := by 
    apply Finset.prod_le_prod 
    · -- Show for all i: 0 ≤ 2 * √(a i)
      intro i hi 
      have h0a := h4a i 
      simpa using h0a 
    · -- Show for all i: (1 + a i) ≥ (2 * √(a i))
      intro i hi 
      specialize h2 i 
      simpa using h2

  have h5 : (∏ i, (2 * Real.sqrt (a i)) ) = 2^n * (∏ i, Real.sqrt (a i)) := by 
    calc 
      ∏ i, (2 * Real.sqrt (a i)) 
          = (∏ i, (2 ) ) * (∏ i, Real.sqrt (a i)) := by 
            rw [Finset.prod_mul_distrib] 
      _ = (2^n) * (∏ i, Real.sqrt (a i)) := by 
        simp 
      _ = 2^n * (∏ i, Real.sqrt (a i)) := by 
        ring

  have h2a : (∏ i, Real.sqrt (a i)) > 0 := by 
    apply Finset.prod_pos 
    intro i hi 
    have h5b : 0 < Real.sqrt (a i) := h3a i 
    linarith

  have h8 : (∏ i, Real.sqrt (a i)) = 1 := by 
    have ha2 : ((∏ i, Real.sqrt (a i)) ) ^ 2 = (∏ i, (a i)) := by 
      calc 
        ((∏ i, Real.sqrt (a i)) ) ^ 2 
          = ∏ i, ( (Real.sqrt (a i) ) ^ 2 ) := by 
            rw [Finset.prod_pow] 
        _ = ∏ i, (a i) := by 
          apply Finset.prod_congr (by rfl)
          intro i hi 
          have ha_i_pos : 0 < a i := h₀ i 
          have h10a : (Real.sqrt (a i) ) ^ 2 = a i := Real.sq_sqrt (by linarith) 
          simpa using h10a 
    rw [h₁] at ha2 
    have ha3 : (∏ i, Real.sqrt (a i) ) = 1 := by 
      nlinarith [show (∏ i, Real.sqrt (a i)) > 0 by simpa using h2a]
    exact_mod_cast ha3

  have h6 : (∏ i, (1 + a i) ) ≥ (∏ i, (2 * Real.sqrt (a i)) ) := h3 
  have h7a : (∏ i, (2 * Real.sqrt (a i)) ) = 2^n * (∏ i, Real.sqrt (a i)) := h5

  rw [h7a, h8] at h6 
  have h9a : (∏ i, (1 + a i) ) ≥ (2^n : ℝ) := by 
    linarith

  exact_mod_cast h9a