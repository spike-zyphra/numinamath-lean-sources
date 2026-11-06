import Mathlib

theorem algebra_168940 (θ : ℝ) (h : ∃ x : ℝ, (3 - 3^(-abs (x - 3)))^2 = 3 - Real.cos θ) :
    θ = (2 * ⌊θ / (2 * Real.pi)⌋ + 1) * Real.pi := by
  rcases h with ⟨x, hx⟩
  have h1 : 2 ≤ (3 - (3 : ℝ) ^ (-abs (x - 3) : ℝ)) := by
    have h2 : (3 : ℝ) ^ (-abs (x - 3) : ℝ) ≤ 1 := by
      have h3 : -abs (x - 3) ≤ (0 : ℝ) := by 
        linarith [abs_nonneg (x - 3)]
      have h4 : (3 : ℝ) ^ (-abs (x - 3) : ℝ) ≤ (3 : ℝ) ^ (0 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num) 
        linarith
      have h5 : (3 : ℝ) ^ (0 : ℝ) = 1 := by 
        norm_num
      linarith [h5]
    linarith
  have h2 : (3 - (3 : ℝ) ^ (-abs (x - 3) : ℝ)) ^ 2 ≥ 4 := by
    nlinarith [sq_nonneg ((3 : ℝ) ^ (-abs (x - 3) : ℝ) - 1)]
  have h3 : 3 - Real.cos θ ≥ 4 := by 
    nlinarith [Real.cos_le_one θ, Real.neg_one_le_cos θ, h2, hx]
  have h4 : Real.cos θ = -1 := by 
    nlinarith [Real.cos_le_one θ, Real.neg_one_le_cos θ, h3]
  have h5 : ∃ k : ℤ, θ = (2 * k + 1) * Real.pi := by
    have h6 : Real.cos θ = -1 := h4 
    have h7 : ∃ k : ℤ, θ = (2 * k + 1) * Real.pi := by 
      have h8 : Real.cos θ = -1 := h6 
      have : ∃ k : ℤ, θ = (2 * k + 1) * Real.pi := by 
        rw [Real.cos_eq_neg_one_iff] at h8 
        rcases h8 with ⟨k, hk⟩ 
        use k 
        all_goals 
          linarith 
      exact_mod_cast this 
    exact_mod_cast h7 
  rcases h5 with ⟨k, hk⟩ 
  have hk' : θ / (2 * Real.pi) = (k + 1 / 2 : ℝ) := by 
    field_simp [Real.pi_pos] at * 
    nlinarith [hk, Real.pi_pos]
  have hk'' : ⌊θ / (2 * Real.pi)⌋ = k := by 
    rw [hk']
    simp [Int.floor_eq_iff, Real.pi_pos] 
    all_goals 
      try { norm_num } 
      all_goals 
        try { linarith } 
  rw [hk'']
  nlinarith [hk, Real.pi_pos]