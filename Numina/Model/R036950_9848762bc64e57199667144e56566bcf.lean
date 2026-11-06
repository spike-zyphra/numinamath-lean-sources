import Mathlib

open Real

theorem inequalities_115066 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 1) :
    9 / 4 ≤ 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) ∧
    1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) ≤ 5 / 2 := by

  constructor
  · -- Prove 9/4 ≤ 1/(1+a) + 1/(1+b) + 1/(1+c)
    have ha1 : 0 < 1 + a := by linarith
    have hb1 : 0 < 1 + b := by linarith
    have hc1 : 0 < 1 + c := by linarith
    have h1 : 9 / 4 ≤ 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) := by
      have h6 : 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) - 9 / 4 ≥ 0 := by
        have h7 : 0 < (1 + a) * (1 + b) * (1 + c) := by positivity
        have h7' : (1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) - 9 / 4) = 
          ( (1 + b) * (1 + c) * 4 + (1 + a) * (1 + c) * 4 + (1 + a) * (1 + b) * 4 - 9 * ((1 + a) * (1 + b) * (1 + c) ) ) / (4 * ((1 + a) * (1 + b) * (1 + c) ) ) := by 
          field_simp 
          ring
        rw [h7']
        apply div_nonneg
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a - 1 / 3), sq_nonneg (b - 1 / 3), sq_nonneg (c - 1 / 3),
          h, mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ b by linarith),
          mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ c by linarith),
          mul_nonneg (show (0 : ℝ) ≤ b by linarith) (show (0 : ℝ) ≤ c by linarith)
        ]
        positivity
      linarith 
    exact h1
  · -- Prove 1/(1+a) + 1/(1+b) + 1/(1+c) ≤ 5/2
    have ha1 : 0 < 1 + a := by linarith
    have hb1 : 0 < 1 + b := by linarith
    have hc1 : 0 < 1 + c := by linarith
    have h2 : 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) - (5 / 2) ≤ 0 := by
      have h7 : 0 < (1 + a) * (1 + b) * (1 + c) := by positivity
      have h8 : ( (1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) ) - (5 / 2) ) = 
        ( (1 + b) * (1 + c) * 2 + (1 + a) * (1 + c) * 2 + (1 + a) * (1 + b) * 2 - 5 * ((1 + a) * (1 + b) * (1 + c) ) ) / (2 * ((1 + a) * (1 + b) * (1 + c) ) ) := by 
        field_simp
        ring 
      rw [h8]
      apply div_nonpos_of_nonpos_of_nonneg
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b), sq_nonneg (c),
        sq_nonneg (a), sq_nonneg (b - 1), sq_nonneg (c),
        sq_nonneg (a), sq_nonneg (b), sq_nonneg (c - 1),
        h, mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ b by linarith),
        mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ c by linarith),
        mul_nonneg (show (0 : ℝ) ≤ b by linarith) (show (0 : ℝ) ≤ c by linarith)
      ]
      positivity
    linarith