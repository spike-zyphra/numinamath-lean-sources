import Mathlib

theorem inequalities_601354 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsum : a + b + c ≤ 3) :
    a / (1 + a ^ 2) + b / (1 + b ^ 2) + c / (1 + c ^ 2) ≤ 3 / 2 ∧
    3 / 2 ≤ 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) := by
  constructor
  · -- Prove the first inequality
    have h1 : a / (1 + a ^ 2) ≤ 1 / 2 := by 
      have h1 : 0 < 1 + a ^ 2 := by nlinarith [sq_nonneg a]
      apply (div_le_iff₀ h1).mpr 
      nlinarith [sq_nonneg (a - 1)]
    have h2 : b / (1 + b ^ 2) ≤ 1 / 2 := by 
      have h2 : 0 < 1 + b ^ 2 := by nlinarith [sq_nonneg b]
      apply (div_le_iff₀ h2).mpr 
      nlinarith [sq_nonneg (b - 1)]
    have h3 : c / (1 + c ^ 2) ≤ 1 / 2 := by 
      have h3 : 0 < 1 + c ^ 2 := by nlinarith [sq_nonneg c]
      apply (div_le_iff₀ h3).mpr 
      nlinarith [sq_nonneg (c - 1)]
    linarith
  · -- Prove the second inequality
    have h2 : 0 < 1 + a := by linarith 
    have h3 : 0 < 1 + b := by linarith 
    have h4 : 0 < 1 + c := by linarith 
    have h5 : 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) ≥ 3 / 2 := by 
      have h6 : 0 < (1 + a) * (1 + b) * (1 + c) := by positivity 
      have h7 : 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) - 3 / 2 ≥ 0 := by
        have h8 : 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) - 3 / 2 =
            (2 * (1 + b) * (1 + c) + 2 * (1 + a) * (1 + c) + 2 * (1 + a) * (1 + b) - 3 * (1 + a) * (1 + b) * (1 + c) ) / (2 * (1 + a) * (1 + b) * (1 + c) ) := by 
          field_simp 
          ring 
        rw [h8] at *
        apply div_nonneg 
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          sq_nonneg (a + b + c - 3), 
          mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ b by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ c by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ b by linarith) (show (0 : ℝ) ≤ c by linarith)
        ]
        all_goals positivity 
      nlinarith 
    linarith