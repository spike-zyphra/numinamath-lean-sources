import Mathlib

theorem algebra_105505 {a b c : ℕ} (ha : a + 2 * b + 3 * c + 21 = 4 * (Real.sqrt (a + 1) - 1) + 6 * (Real.sqrt (2 * b + 1) - 1) + 10 * (Real.sqrt (3 * c + 1) - 1)) :
    a = 3 ∧ b = 4 ∧ c = 8 ∧ ¬ ∃ n, n^2 = (100 * a + 10 * b + c)^2016 + (100 * a + 10 * c + b)^2016 := by 
  have h1 : (Real.sqrt (a + 1) : ℝ) ≥ 0 := by positivity
  have h2 : (Real.sqrt (2 * b + 1) : ℝ) ≥ 0 := by positivity
  have h3 : (Real.sqrt (3 * c + 1) : ℝ) ≥ 0 := by positivity
  have eq1 : (Real.sqrt (a + 1)) ^ 2 = (a + 1 : ℝ) := Real.sq_sqrt (by linarith)
  have eq2 : (Real.sqrt (2 * b + 1)) ^ 2 = (2 * b + 1 : ℝ) := Real.sq_sqrt (by linarith)
  have eq3 : (Real.sqrt (3 * c + 1)) ^ 2 = (3 * c + 1 : ℝ) := Real.sq_sqrt (by linarith)
  have h_eq : (Real.sqrt (a + 1) - 2 : ℝ) ^ 2 + (Real.sqrt (2 * b + 1) - 3 : ℝ) ^ 2 + (Real.sqrt (3 * c + 1) - 5 : ℝ) ^ 2 = 0 := by
    nlinarith [Real.sqrt_nonneg (a + 1 : ℝ), Real.sqrt_nonneg (2 * b + 1 : ℝ), Real.sqrt_nonneg (3 * c + 1 : ℝ), 
        sq_nonneg (Real.sqrt (a + 1 : ℝ) - 2), sq_nonneg (Real.sqrt (2 * b + 1 : ℝ) - 3), sq_nonneg (Real.sqrt (3 * c + 1 : ℝ) - 5)]
  have h4 : Real.sqrt (a + 1 : ℝ) - 2 = 0 := by 
    nlinarith [sq_nonneg (Real.sqrt (a + 1 : ℝ) - 2), sq_nonneg (Real.sqrt (2 * b + 1 : ℝ) - 3), sq_nonneg (Real.sqrt (3 * c + 1 : ℝ) - 5), h_eq]
  have h5 : Real.sqrt (2 * b + 1 : ℝ) - 3 = 0 := by 
    nlinarith [sq_nonneg (Real.sqrt (a + 1 : ℝ) - 2), sq_nonneg (Real.sqrt (2 * b + 1 : ℝ) - 3), sq_nonneg (Real.sqrt (3 * c + 1 : ℝ) - 5), h_eq]
  have h6 : Real.sqrt (3 * c + 1 : ℝ) - 5 = 0 := by 
    nlinarith [sq_nonneg (Real.sqrt (a + 1 : ℝ) - 2), sq_nonneg (Real.sqrt (2 * b + 1 : ℝ) - 3), sq_nonneg (Real.sqrt (3 * c + 1 : ℝ) - 5), h_eq]
  have h7 : Real.sqrt (a + 1 : ℝ) = 2 := by linarith
  have h8 : Real.sqrt (2 * b + 1 : ℝ) = 3 := by linarith
  have h9 : Real.sqrt (3 * c + 1 : ℝ) = 5 := by linarith
  have ha' : (a + 1 : ℝ) = 4 := by 
    calc 
      (a + 1 : ℝ) = (Real.sqrt (a + 1 : ℝ)) ^ 2 := by rw [Real.sq_sqrt]; linarith
      _ = (2 : ℝ) ^ 2 := by rw [h7]
      _ = (4 : ℝ) := by norm_num
  have hb' : (2 * b + 1 : ℝ) = 9 := by 
    calc 
      (2 * b + 1 : ℝ) = (Real.sqrt (2 * b + 1 : ℝ)) ^ 2 := by rw [Real.sq_sqrt]; linarith
      _ = (3 : ℝ) ^ 2 := by rw [h8]
      _ = (9 : ℝ) := by norm_num
  have hc' : (3 * c + 1 : ℝ) = 25 := by 
    calc 
      (3 * c + 1 : ℝ) = (Real.sqrt (3 * c + 1 : ℝ)) ^ 2 := by rw [Real.sq_sqrt]; linarith
      _ = (5 : ℝ) ^ 2 := by rw [h9]
      _ = (25 : ℝ) := by norm_num
  have ha1 : a = 3 := by 
    have h10 : (a : ℝ) + 1 = 4 := by linarith
    have h11 : (a : ℝ) = 3 := by linarith
    exact_mod_cast h11
  have hb1 : b = 4 := by 
    have h12 : (2 * b : ℝ) + 1 = 9 := by linarith
    have h13 : (2 * b : ℝ) = 8 := by linarith
    have h14 : (b : ℝ) = 4 := by linarith
    exact_mod_cast h14
  have hc1 : c = 8 := by 
    have h15 : (3 * c : ℝ) + 1 = 25 := by linarith
    have h16 : (3 * c : ℝ) = 24 := by linarith
    have h17 : (c : ℝ) = 8 := by linarith
    exact_mod_cast h17
  constructor 
  · exact ha1 
  constructor 
  · exact hb1 
  constructor 
  · exact hc1 
  · -- Prove that \( \overline{abc}^{2016} + \overline{acb}^{2016} \) is not a perfect square.
    intro h 
    rcases h with ⟨n, hn⟩ 
    rw [ha1, hb1, hc1] at hn
    have h10 : (n : ℕ) ^ 2 = (348 : ℕ) ^ 2016 + (384 : ℕ) ^ 2016 := by 
      norm_num at hn ⊢ 
      linarith 
    have h11 : n ^ 2 % 5 = 0 ∨ n ^ 2 % 5 = 1 ∨ n ^ 2 % 5 = 4 := by 
      have h12 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by 
        omega 
      rcases h12 with (h | h | h | h | h) <;> 
        simp [Nat.pow_mod, h] 
    have h10' : (348 ^ 2016 + 384 ^ 2016) % 5 = 2 := by
      norm_num
    have h13 : (n ^ 2) % 5 = 2 := by 
      omega 
    omega