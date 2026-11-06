import Mathlib

theorem number_theory_8369 (x : ℕ → ℤ) (hx1 : x 1 = 1) (hxn : ∀ n, x (n + 1) = 4 * x n + ⌊√11 * x n⌋) :
    (x 2024) % 10 = 3 := by
  exfalso 
  have h1 := hxn 0
  norm_num [hx1] at h1 
  -- Now h1 is: 1 = 4 * x 0 + ⌊√11 * ↑(x 0)⌋, contradictory
  -- From the recurrence relation, we can't get 1 here
  -- There is no integer solution to 1 = 4 * x0 + ⌊√11 * x0⌋
  -- √11 ≈ 3.3166
  -- So ⌊√11 * x0⌋ ≤ 3 * x0 + 3
  -- So 1 = 4 * x0 + ⌊√11 * x0⌋ ≤ 4 *x0 + 3*x0 + 3 = 7*x0 + 3
  -- So 1 ≤ 7*x0 + 3
  -- But contradiction if x0 = 0
  -- If x0 = 0, then 1 = 4*(0) + ⌊√11*(0)⌋ ⇒ 1 = 0 + ⌊0⌋ ⇒ 1 = 0
  -- It is contradiction.
  all_goals
    try { 
      have h0 : x 0 ≤ 0 := by
        by_contra h
        push_neg at h
        have : x 0 ≥ 1 := by omega 
        have h2 : (4 * x 0 : ℤ) + ⌊√11 * (x 0 : ℤ)⌋ ≥ 4 * 1 + 1 := by
          have h11 : ⌊√11 * (x 0 : ℤ)⌋ ≥ 1 := by
            have h12 : √11 ≥ 3 := by nlinarith [Real.sqrt_nonneg (11 : ℝ), Real.sq_sqrt (show 0 ≤ (11 : ℝ) by norm_num)]
            have h13 : √11 * (x 0 : ℤ) ≥ (3 : ℝ) * (1 : ℝ) := by
              have h14 : (x 0 : ℝ) ≥ (1 : ℝ) := by exact_mod_cast this
              nlinarith [Real.sqrt_nonneg (11 : ℝ)]
            have h15 : ⌊√11 * (x 0 : ℤ)⌋ ≥ 1 := by
              have h16 : √11 * (x 0 : ℤ) ≥ 3 := by
                exact_mod_cast h13
              have h17 : ⌊√11 * (x 0 : ℤ)⌋ ≥ ⌊(3 : ℝ)⌋ := by
                apply Int.floor_le_floor
                linarith
              norm_num at h17 ⊢
              omega
            omega
          omega
        nlinarith 
      have h10 : x 0 ≤ 0 := h0
      have h_eq1 : x 0 = 0 := by 
        by_contra h
        push_neg at h
        have h11 : x 0 < 0 := by
          omega
        have : x 0 ≤ -1 := by 
          omega
        have h21 : (4 * x 0 : ℤ) + ⌊√11 * (x 0 : ℤ)⌋ ≤ -1 * 1 + (-1) := by
          have h00 : (x 0 : ℤ) ≤ -1 := by 
            omega
          have h11 : ⌊√11 * (x 0 : ℤ)⌋ ≤ -1 := by 
            have h111 : √11 * (x 0 : ℤ) ≤ (-3 : ℝ) := by
              have h1111 : (x 0 : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast h00
              nlinarith [Real.sqrt_nonneg (11 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num)]
            have h112 : ⌊√11 * (x 0 : ℤ)⌋ ≤ (-1 : ℤ) := by 
              have h113 : √11 * (x 0 : ℤ) ≤ (-3 : ℝ) := h111
              have h114 : (⌊√11 * (x 0 : ℤ)⌋ : ℝ) ≤ √11 * (x 0 : ℤ) := by
                exact Int.floor_le (√11 * (x 0 : ℤ))
              have h115 : (⌊√11 * (x 0 : ℤ)⌋ : ℝ) ≤ (-3 : ℝ) := by 
                linarith [h114, h111]
              have h116 : ⌊√11 * (x 0 : ℤ)⌋ ≤ -3 := by
                by_contra h0
                push_neg at h0
                have : ⌊√11 * (x 0 : ℤ)⌋ ≥ -2 := by 
                  omega
                have h117 : (⌊√11 * (x 0 : ℤ)⌋ : ℝ) ≥ (-2 : ℝ) := by
                  exact_mod_cast this
                linarith
              omega
            omega
          linarith 
        nlinarith 
      rw [h_eq1] at h1 
      norm_num at h1
      all_goals
        nlinarith 
    }
    <;> try { 
      omega 
    }