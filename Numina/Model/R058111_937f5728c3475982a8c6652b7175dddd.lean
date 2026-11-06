import Mathlib

theorem number_theory_110195 (a d : ℝ) (h₀ : a = Real.sqrt 2) (h₁ : d ≠ 0)
    (h₂ : ∃ n, Real.sqrt 5 = a + d * n ∧ Real.sqrt 7 = Real.sqrt 5 + d * n) :
    False := by
  rcases h₂ with ⟨n, h₃, h₄⟩
  rw [h₀] at h₃
  have eq1 : Real.sqrt 5 - Real.sqrt 2 = d * n := by linarith 
  have eq2 : Real.sqrt 7 - Real.sqrt 5 = d * n := by linarith 
  have eq3 : Real.sqrt 7 + Real.sqrt 2 = 2 * Real.sqrt 5 := by 
    linarith 
  have h5 : (Real.sqrt 7 + Real.sqrt 2) ^ 2 = (2 * Real.sqrt 5) ^ 2 := by 
    rw [eq3]
  have h6 : (Real.sqrt 7 + Real.sqrt 2) ^ 2 = 9 + 2 * (Real.sqrt 7 * Real.sqrt 2) := by
    calc 
      (Real.sqrt 7 + Real.sqrt 2) ^ 2 = Real.sqrt 7 ^ 2 + Real.sqrt 2 ^ 2 + 2 * (Real.sqrt 7 * Real.sqrt 2) := by ring 
      _ = (7) + (2) + 2 * (Real.sqrt 7 * Real.sqrt 2) := by 
        have h7 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
        have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        rw [h7, h2]
      _ = 9 + 2 * (Real.sqrt 7 * Real.sqrt 2) := by ring 
  have h7 : (2 * Real.sqrt 5) ^ 2 = 20 := by 
    calc 
      (2 * Real.sqrt 5) ^ 2 = 4 * (Real.sqrt 5 ^ 2) := by ring 
      _ = 4 * 5 := by rw [Real.sq_sqrt (by norm_num)]
      _ = 20 := by norm_num 
  have h8 : 9 + 2 * (Real.sqrt 7 * Real.sqrt 2) = 20 := by
    linarith [h5, h6, h7]
  have h9 : Real.sqrt 7 * Real.sqrt 2 = 11 / 2 := by
    nlinarith
  have h10 : Real.sqrt 7 * Real.sqrt 2 = Real.sqrt 14 := by
    calc 
      Real.sqrt 7 * Real.sqrt 2 = Real.sqrt (7 * 2) := by rw [Real.sqrt_mul (by norm_num)]
      _ = Real.sqrt 14 := by norm_num 
  have h11 : Real.sqrt 14 = 11 / 2 := by
    linarith [h9, h10]
  have h12 : Real.sqrt 14 ^ 2 = 14 := Real.sq_sqrt (by norm_num)
  have h13 : (11 / 2 : ℝ) ^ 2 = 121 / 4 := by norm_num 
  have h14 : Real.sqrt 14 ^ 2 = (11 / 2) ^ 2 := by 
    rw [h11]
  rw [h12, h13] at h14
  norm_num at h14 
  all_goals linarith