import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_29142 (θ : ℝ) (m : ℕ) :
  |sin (m * θ)| ≤ m * |sin θ| := by
    have h1 : ∀ m : ℕ, |sin (m * θ)| ≤ m * |sin θ| := by 
      intro m
      induction m with
      | zero => 
        simp [Nat.cast_zero, mul_zero, zero_mul]
      | succ m ih => 
        have h2 : sin ((↑(m + 1 : ℕ) : ℝ) * θ) = sin ((↑m : ℝ) * θ + θ) := by 
          simp [mul_add, add_mul, mul_assoc]
          <;> ring_nf <;> simp [Nat.cast_add, mul_add, add_mul]
          <;> ring_nf <;> simp [Nat.cast_add]
        have h3 : sin ((↑m : ℝ) * θ + θ) = sin ((↑m : ℝ) * θ) * cos θ + cos ((↑m : ℝ) * θ) * sin θ := by 
          rw [sin_add]
          <;> simp [Nat.cast_add]
          <;> ring_nf <;> simp [Nat.cast_add, mul_add, add_mul]
          <;> ring_nf <;> simp [Nat.cast_add]
        -- Use h2 and h3 to rewrite the goal
        rw [h2, h3]
        have h4 : |sin ((↑m : ℝ) * θ) * cos θ + cos ((↑m : ℝ) * θ) * sin θ| ≤ |sin ((↑m : ℝ) * θ) * cos θ| + |cos ((↑m : ℝ) * θ) * sin θ| := by 
          apply abs_add
        have h8 : |sin ((↑m : ℝ) * θ) * cos θ| = |sin ((↑m : ℝ) * θ)| * |cos θ| := by 
          rw [abs_mul]
        have h9 : |cos ((↑m : ℝ) * θ) * sin θ| = |cos ((↑m : ℝ) * θ)| * |sin θ| := by 
          rw [abs_mul]
          all_goals try tauto
        have hcos1 : |cos ((↑m : ℝ) * θ)| ≤ 1 := by 
          apply abs_le.mpr
          constructor
          all_goals linarith [neg_one_le_cos ((↑m : ℝ) * θ), cos_le_one ((↑m : ℝ) * θ)]
          all_goals nlinarith [neg_one_le_cos ((↑m : ℝ) * θ), cos_le_one ((↑m : ℝ) * θ)]
          all_goals nlinarith [neg_one_le_cos ((↑m : ℝ) * θ), cos_le_one ((↑m : ℝ) * θ)]
        have hsin1 : |sin θ| ≤ 1 := by 
          apply abs_le.mpr
          constructor
          all_goals linarith [neg_one_le_sin θ, sin_le_one θ]
          all_goals nlinarith [neg_one_le_sin θ, sin_le_one θ]
          all_goals nlinarith [neg_one_le_sin θ, sin_le_one θ]
        have hcos2 : |cos θ| ≤ 1 := by 
          apply abs_le.mpr
          constructor
          all_goals linarith [neg_one_le_cos θ, cos_le_one θ]
          all_goals nlinarith [neg_one_le_cos θ, cos_le_one θ]
          all_goals nlinarith [neg_one_le_cos θ, cos_le_one θ]
        have h17 : |sin ((↑m : ℝ) * θ) * cos θ| ≤ |sin ((↑m : ℝ) * θ)| := by 
          calc 
            |sin ((↑m : ℝ) * θ) * cos θ| = |sin ((↑m : ℝ) * θ)| * |cos θ| := by 
              rw [abs_mul]
            _ ≤ |sin ((↑m : ℝ) * θ)| * 1 := by 
              apply mul_le_mul_of_nonneg_left
              linarith [hcos2]
              positivity 
            _ = |sin ((↑m : ℝ) * θ)| := by 
              ring_nf 
        have h18 : |cos ((↑m : ℝ) * θ) * sin θ| ≤ |sin θ| := by 
          calc 
            |cos ((↑m : ℝ) * θ) * sin θ| = |cos ((↑m : ℝ) * θ)| * |sin θ| := by 
              rw [abs_mul]
            _ ≤ 1 * |sin θ| := by 
              apply mul_le_mul_of_nonneg_right
              linarith [hcos1]
              positivity
            _ = |sin θ| := by 
              ring_nf
        have h24 : |sin ((↑m : ℝ) * θ) * cos θ| + |cos ((↑m : ℝ) * θ) * sin θ| ≤ |sin ((↑m : ℝ) * θ)| + |sin θ| := by 
          linarith [h17, h18]
        have h28 : |sin θ| ≥ 0 := by 
          apply abs_nonneg 
        have h29 : |sin ((↑m : ℝ) * θ)| ≤ (↑m : ℕ) * |sin θ| := by 
          simpa using ih 
        have h30 : |sin ((↑m : ℝ) * θ) * cos θ + cos ((↑m : ℝ) * θ) * sin θ| ≤ (↑m + 1 : ℝ) * |sin θ| := by 
          linarith [h4, h8, h9, h24, h28, h29, hsin1]
        norm_num at h30 ⊢ 
        all_goals nlinarith
    specialize h1 m 
    simpa using h1