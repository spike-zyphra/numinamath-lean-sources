import Mathlib

theorem algebra_252455 {f : ℕ → ℝ} (h : ∀ n, f (n + 1) = (2 * f n + 3) / (f n + 2))
    (hf : f 0 = 1 / 4) :
    ∀ n, 0 < f n ∧ f n < Real.sqrt 3 := by 
  intro n
  induction n with
  | zero =>
    constructor
    · -- Prove that 0 < f 0
      rw [hf]
      norm_num
    · -- Prove that f 0 < Real.sqrt 3
      rw [hf]
      have h4 : (1 / 4 : ℝ) < Real.sqrt 3 := by
        have h6 : Real.sqrt (1 / 16 : ℝ) = 1 / 4 := by 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
        have h7 : Real.sqrt (1 / 16 : ℝ) < Real.sqrt 3 := by 
          apply Real.sqrt_lt_sqrt 
          all_goals 
            norm_num 
        linarith [h6, h7]
      linarith [h4]
  | succ k ih =>
    rcases ih with ⟨hk1, hk2⟩
    constructor
    · -- Prove that 0 < f (k + 1)
      rw [h k]
      have h3 : 0 < f k := hk1
      have h4 : 0 < (f k + 2 : ℝ) := by 
        linarith 
      have h5 : 0 < (2 * f k + 3 : ℝ) := by 
        nlinarith 
      apply div_pos 
      all_goals 
        linarith 
    · -- Prove that f (k + 1) < Real.sqrt 3
      rw [h k]
      have h3 : 0 < f k := hk1
      have hk2' : f k < Real.sqrt 3 := hk2 
      have eq5 : (2 * f k + 3 : ℝ) / (f k + 2) < Real.sqrt 3 := by 
        have h6 : (2 * f k + 3 : ℝ) < Real.sqrt 3 * (f k + 2) := by 
          have h9 : Real.sqrt 3 > 0 := by 
            positivity 
          nlinarith [Real.sqrt_nonneg 3, sq_pos_of_pos h9, 
            Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), 
            sq_nonneg ((f k - 1 / 4 : ℝ)), 
            sq_nonneg ((Real.sqrt 3 - f k) : ℝ), 
            sq_nonneg ((f k + 2 - 2) : ℝ), 
            mul_pos (show 0 < (f k + 2 : ℝ) by linarith) (show 0 < (Real.sqrt 3 : ℝ) by positivity)]
        have h7 : 0 < (f k + 2 : ℝ) := by 
          linarith 
        apply (div_lt_iff₀' h7).mpr 
        nlinarith 
      linarith [eq5]