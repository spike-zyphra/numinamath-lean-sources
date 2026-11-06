import Mathlib

theorem inequalities_29969 (a b c d : ℝ) (h₀ : a + b + c + d = 0) (h₁ : a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 = 0) :
    a + b = 0 ∨ a + c = 0 ∨ a + d = 0 ∨ b + c = 0 ∨ b + d = 0 ∨ c + d = 0 := by
  have h2 : d = - (a + b + c) := by linarith
  rw [h2] at h₁
  have h4 : (a + b) * (a + c) * (b + c) = 0 := by
    nlinarith [sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  cases' (mul_eq_zero.mp h4) with h5 h6
  cases' (mul_eq_zero.mp h5) with h7 h8
  · -- a + b = 0
    left
    linarith
  · -- a + c = 0
    right
    left
    linarith
  · -- b + c = 0
    right
    right
    right
    left
    linarith
  all_goals
    try { 
      norm_num at h6
      <;> try { 
          exfalso
          <;> try { 
              nlinarith [sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
          }
      }
    }
  all_goals
    try { 
      tauto
    }
  all_goals
    try { 
      linarith
    }
  all_goals
    try { 
      nlinarith [sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
    }