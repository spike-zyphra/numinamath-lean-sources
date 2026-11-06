import Mathlib

theorem algebra_1180 {a b : ℝ} (h : a ≠ b ∧ 1 / (1 + a) - 1 / (1 + b) = 1 / (b - a)) : (1 + b) / (1 + a) + (1 + a) / (1 + b) = 3 := by
  rcases h with ⟨ha1, he⟩
  have h1 : 1 + a ≠ 0 := by
    by_contra h2
    have h1' : a = -1 := by linarith
    rw [show 1 + a = (0 : ℝ) by linarith] at he
    -- simplifying he using 1 + a = 0
    have h2' : b - a ≠ 0 := by 
      intro h0
      have : a = b := by linarith
      contradiction
    have h3 : 1 + b ≠ 0 := by 
      by_contra h0
      have h2 : b = -1 := by linarith
      have h4 : a = b := by
        have h5 : a = -1 := h1'
        have h6 : b = -1 := h2
        linarith
      contradiction 
    -- field_simp on he to simplify, cross multiply to verify what results
    field_simp [h3, h2'] at he
    <;> try { 
      have h5 : b = -1 := by
        nlinarith [sq_nonneg (b + 1), sq_nonneg (a), sq_pos_of_ne_zero (show (b - a : ℝ) ≠ 0 by
          intro h0
          have : a = b := by
            linarith
          contradiction
        )
        ]
      have h5' : b = -1 := h5
      have h4 : a = -1 := h1'
      have h6 : a = b := by
        nlinarith [h5', h4]
      contradiction 
    }
    <;> try { 
      all_goals 
        nlinarith [sq_nonneg (b - a), sq_nonneg (b + 1), sq_nonneg (a + 1)]
      <;> try { tauto }
    }
  have h2 : 1 + b ≠ 0 := by
    by_contra h3
    have h2' : b = -1 := by linarith
    rw [show 1 + b = (0 : ℝ) by linarith] at he
    have h3' : b - a ≠ 0 := by
      intro h0
      have : a = b := by linarith
      contradiction
    have h4 : 1 + a ≠ 0 := h1
    field_simp [h4, h3'] at he
    <;> try { 
      have h4' : a = -1/2 := by
        nlinarith [sq_nonneg (b * a), sq_pos_of_ne_zero (show (b - a : ℝ) ≠ 0 by
          intro h0
          have : a = b := by
            linarith
          contradiction
        ), sq_nonneg (b), sq_nonneg (a), sq_nonneg ((a + 1) * (b + 1))]
      have h4' : a = -1/2 := h4'
      have h5 : b = -1 := h2'
      -- with a = -1/2 and b = -1, he simplifies to a undefined side case
      -- however it still holds mathematically
      norm_num [h4', h5] at he ⊢ <;> try { 
        exfalso 
        <;> try { 
          nlinarith [sq_pos_of_ne_zero (show (b - a : ℝ) ≠ 0 by
            intro h0
            have : a = b := by
              linarith
            contradiction
          ), sq_pos_of_ne_zero h1]
        }
      }
    }
    <;> try { 
      all_goals
        nlinarith [sq_nonneg (b - a), sq_nonneg (b * a)]
      <;> try { 
        tauto 
        <;> tauto 
        <;> tauto 
      }
    }
  have h3 : b - a ≠ 0 := by
    intro h0
    have : a = b := by linarith
    contradiction 
  -- We have cross multiplied from the equation.
  -- need to compute (1 + b) / (1 + a) + (1 + a) / (1 + b)
  -- via field cross multiply as well
  have h4 : (b - a) * (b - a) = (1 + a) * (1 + b) := by 
    field_simp [h1, h2, h3] at he 
    nlinarith [sq_nonneg (b - a), sq_nonneg (a + 1), sq_nonneg (b + 1)]
  have h5 : (1 + b) / (1 + a) + (1 + a) / (1 + b) = 3 := by
    field_simp [h1, h2]
    <;> nlinarith [sq_nonneg (b - a), sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (b * a), sq_nonneg ((a + 1) * (b + 1)), sq_nonneg (a - b), h4]
    <;> try { 
      nlinarith 
      <;> try { 
        nlinarith 
      }
    }
    <;> try { 
      nlinarith [sq_pos_of_ne_zero (show (b - a : ℝ) ≠ 0 by
        intro h0
        have : a = b := by 
          linarith 
        contradiction
      ), sq_pos_of_ne_zero h1, sq_pos_of_ne_zero h2]
    }
  exact h5
  all_goals
    try { 
      tauto 
      <;> try { 
        tauto 
      }
    }
    <;> try { 
      nlinarith [sq_pos_of_ne_zero (show (b - a : ℝ) ≠ 0 by
          intro h0
          have : a = b := by 
            linarith 
          contradiction
        ), sq_pos_of_ne_zero h1, sq_pos_of_ne_zero h2, sq_nonneg (a - b), sq_nonneg (a * b)]
    }