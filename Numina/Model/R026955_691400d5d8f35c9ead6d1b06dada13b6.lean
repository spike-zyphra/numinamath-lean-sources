import Mathlib

theorem algebra_326005 {a : ℕ → ℝ} (ha1 : a 1 = 1)
    (han : ∀ n ≥ 1, a (n + 1) = 4 * a n + 4 * Real.sqrt (a n) + 1) :
    ∀ n ≥ 1, a n = 2^(2 * n) - 2^(n + 1) + 1 := by
  intro n hn
  induction n with
  | zero =>
    exfalso
    linarith
  | succ n ih =>
    cases n with
    | zero =>
      rw [ha1]
      norm_num
    | succ n =>
      have h1 := ih (by linarith)
      have h2 : a (n + 2) = 4 * a (n + 1) + 4 * Real.sqrt (a (n + 1)) + 1 := by 
        specialize han (n + 1) (by linarith)
        simpa using han
      rw [show n + 2 = (n + 1) + 1 by omega]
      rw [h2]
      have h3 : a (n + 1) = 2 ^ (2 * (n + 1)) - 2 ^ ((n + 1) + 1) + 1 := by 
        simpa using h1
      have h4 : Real.sqrt (a (n + 1)) = (2 ^ (n + 1) - 1 : ℝ) := by
        rw [h3]
        have h5 : (2 ^ (2 * (n + 1)) - 2 ^ ((n + 1) + 1) + 1 : ℝ) = ((2 ^ (n + 1) - 1 : ℝ) ) ^ 2 := by 
          ring_nf
        rw [h5]
        have h6 : (2 ^ (n + 1) - 1 : ℝ) ≥ (0 : ℝ) := by
          have h7 : (2 : ℝ) ^ (n + 1) ≥ (1 : ℝ) := by
            have h8 : ∀ (n : ℕ), (2 : ℝ) ^ (n + 1) ≥ (1 : ℝ) := by 
              intro n 
              induction n with
              | zero =>
                norm_num 
              | succ n ih => 
                simp [pow_add, pow_mul] at ih ⊢ 
                all_goals 
                nlinarith 
            specialize h8 n 
            simpa using h8 
          have h9 : (2 ^ (n + 1) - 1 : ℝ) ≥ (0 : ℝ) := by 
            linarith [h7] 
          linarith 
        have h7 : Real.sqrt (( (2 ^ (n + 1) - 1 : ℝ) ) ^ 2) = (2 ^ (n + 1) - 1 : ℝ) := by 
          rw [Real.sqrt_sq (show (2 ^ (n + 1) - 1 : ℝ) ≥ (0 : ℝ) by 
            linarith [h6]
          )] 
        linarith 
      rw [h4]
      simp [h3] at *
      ring_nf