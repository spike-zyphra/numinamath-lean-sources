import Mathlib

open Real

theorem inequalities_157674 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (b + c) + b / (a + c) + c / (a + b) ≥ 3 / 2 ∧
    (a / (b + c) + b / (a + c) + c / (a + b) = 3 / 2 ↔ a = b ∧ b = c) := by
  constructor
  · -- Prove the inequality $\ge$.
    have h1 : 0 < b + c := by linarith
    have h2 : 0 < a + c := by linarith
    have h3 : 0 < a + b := by linarith
    have h4 : a / (b + c) + b / (a + c) + c / (a + b) - 3 / 2 ≥ 0 := by
      have h5 : 0 < (b + c) * (a + c) * (a + b) := by positivity
      have h6 : a / (b + c) + b / (a + c) + c / (a + b) - 3 / 2 =
                ( 2 * a * (a + c) * (a + b) +
                  2 * b * (b + c) * (a + b) +
                  2 * c * (b + c) * (a + c) - 3 * (b + c) * (a + c) * (a + b) ) / (2 * (b + c) * (a + c) * (a + b)) := by
        field_simp
        ring
      rw [h6]
      apply div_nonneg
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]
      positivity 
    linarith 
  · -- Prove equality holds if and only if conditions
    constructor
    · -- If equality holds, proving $A = B \wedge b = c$
      intro heq 
      have heq1 : 0 < b + c := by linarith 
      have heq2 : 0 < a + c := by linarith 
      have heq3 : 0 < a + b := by linarith 
      have h7 : 2 * a * (a + c) * (a + b) + 2 * b * (b + c) * (a + b) + 2 * c * (b + c) * (a + c) = 3 * (b + c) * (a + c) * (a + b) := by 
        have h5 : 0 < (b + c) * (a + c) * (a + b) := by positivity 
        have h8 : a / (b + c) + b / (a + c) + c / (a + b) - 3 / 2 = 0 := by 
          linarith [heq]
        have h5' : a / (b + c) + b / (a + c) + c / (a + b) - 3 / 2 = 
              ( 2 * a * (a + c) * (a + b) + 2 * b * (b + c) * (a + b) + 2 * c * (b + c) * (a + c) - 3 * (b + c) * (a + c) * (a + b) ) / (2 * (b + c) * (a + c) * (a + b)) := by 
              field_simp 
              ring 
        rw [h5'] at h8 
        field_simp at h8 
        nlinarith 
      have h1 : a - b = 0 := by 
        have eq1 : (a - b) ^ 2 = 0 := by 
          nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
                sq_nonneg (a * b - b * c), sq_nonneg (a * b - a * c), sq_nonneg (a * c - b * c)
            ]
        nlinarith 
      -- Now, prove b = c. This is where we need to fix the previous error.
      have h0' : (b - c) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
              sq_nonneg (a * b - b * c), sq_nonneg (a * c - b * c)
          ]
      have h0 : b - c = 0 := by 
          nlinarith 
      have h1' : a = b := by linarith 
      have h2' : b = c := by linarith
      exact ⟨h1', h2'⟩ 
    · -- Conversely, proving the equality condition with the converging conditions $a = b \wedge b = c \implies a / (b + c) + \ldots = 3 / 2
      rintro ⟨rfl, rfl⟩ 
      field_simp 
      <;> ring