import Mathlib

theorem algebra_315809
    (a : ℕ → ℝ)
    (ha1 : a 1 = 1)
    (han : ∀ n > 0, a (n + 1) = (1 + 2 * a n) / (1 + a n)) :
    ∀ n > 0, a n < (1 + Real.sqrt 5) / 2 := by
  intro n hn
  induction n with
  | zero =>
    exfalso 
    nlinarith 
  | succ n ih =>
    cases n with 
    | zero =>
      rw [ha1]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    | succ n => 
      have h2 := ih (by linarith)
      have h3 : a (n + 1) ≥ 1 := by 
        have h4 : ∀ (n : ℕ), n > 0 → a n ≥ 1 := by
          intro n hn 
          induction n with 
          | zero => 
            exfalso 
            linarith 
          | succ n ih => 
            cases n with 
            | zero => 
              rw [ha1]
              all_goals norm_num 
            | succ n => 
              have h6 := ih (by omega)
              have h7 : a (n + 1 + 1) = (1 + 2 * a (n + 1)) / (1 + a (n + 1)) := by 
                specialize han (n + 1) (by linarith)
                simpa using han 
              rw [h7]
              have h8 : a (n + 1) ≥ 1 := h6 
              have h9 : (1 + 2 * a (n + 1)) / (1 + a (n + 1)) ≥ 1 := by 
                apply (le_div_iff₀ (by linarith)).mpr 
                nlinarith
              linarith
        specialize h4 (n + 1) (by linarith)
        simpa using h4
      have h4 : a (n + 1 + 1) = (1 + 2 * a (n + 1)) / (1 + a (n + 1)) := by 
        specialize han (n + 1) (by omega)
        simpa using han 
      rw [h4]
      have h5 : (1 + 2 * a (n + 1)) / (1 + a (n + 1)) < (1 + Real.sqrt 5) / 2 := by 
        have h6 : a (n + 1) < (1 + Real.sqrt 5) / 2 := h2 
        have h7 : 1 + a (n + 1) > 0 := by 
          nlinarith [h3]
        have h8 : (1 + Real.sqrt 5) / 2 > 0 := by 
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num)]
        apply (div_lt_iff₀ (by linarith)).mpr 
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (a (n + 1) - (1 + Real.sqrt 5) / 2), h6]
      exact h5