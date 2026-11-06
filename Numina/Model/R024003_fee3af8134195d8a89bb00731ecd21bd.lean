import Mathlib

theorem algebra_219369 {a b : ℝ} (hab : a * b ≠ 1) (ha : abs a = 1 ∨ abs b = 1) :
    abs ((a - b) / (1 - a * b)) = 1 := by
  have h1 : abs ((a - b) / (1 - a * b)) = 1 := by
    have h2 : ∀ y : ℝ, y = (a - b) / (1 - a * b) → y ^ 2 = 1 := by
      intro y h_eq
      rcases ha with (ha | hb)
      · -- Case $|a| = 1$
        have ha1 : a = 1 ∨ a = -1 := by
          cases eq_or_eq_neg_of_abs_eq ha with
          | inl h => 
            left; linarith
          | inr h => 
            right; linarith
        cases ha1 with
        | inl ha1 =>
          have eq1 : ((a - b) / (1 - a * b)) ^ 2 = 1 := by
            rw [show a = 1 by linarith [ha1]]
            have h1 : (1 - b : ℝ) ≠ 0 := by
              by_contra h2
              have h3 : b = 1 := by linarith
              have h4 : a * b = 1 := by
                rw [show a = 1 by linarith [ha1]]
                rw [show b = 1 by linarith [h3]]
                all_goals norm_num
              contradiction
            field_simp [h1]
            <;> nlinarith
          have eq2 : y ^ 2 = 1 := by
            rw [h_eq]
            linarith [eq1]
          exact eq2
        | inr ha1 =>
          have eq1 : ((a - b) / (1 - a * b)) ^ 2 = 1 := by
            rw [show a = -1 by linarith [ha1]]
            have h1 : (1 + b : ℝ) ≠ 0 := by
              by_contra h2
              have h3 : b = -1 := by linarith
              have h4 : a * b = 1 := by
                rw [show a = -1 by linarith [ha1]]
                rw [show b = -1 by linarith [h3]]
                all_goals norm_num
              contradiction
            field_simp [h1]
            <;> nlinarith
          have eq2 : y ^ 2 = 1 := by
            rw [h_eq]
            linarith [eq1]
          exact eq2
      · -- Case $|b| = 1$
        have hb1 : b = 1 ∨ b = -1 := by
          cases eq_or_eq_neg_of_abs_eq hb with
          | inl h => 
            left; linarith
          | inr h => 
            right; linarith
        cases hb1 with
        | inl hb1 =>
          have eq1 : ((a - b) / (1 - a * b)) ^ 2 = 1 := by
            rw [show b = 1 by linarith [hb1]]
            have h1 : (1 - a : ℝ) ≠ 0 := by
              by_contra h2
              have h3 : a = 1 := by linarith
              have h4 : a * b = 1 := by
                rw [show a = 1 by linarith [h3]]
                rw [show b = 1 by linarith [hb1]]
                all_goals norm_num
              contradiction
            field_simp [h1]
            <;> nlinarith
          have eq2 : y ^ 2 = 1 := by
            rw [h_eq]
            linarith [eq1]
          exact eq2
        | inr hb1 =>
          have eq1 : ((a - b) / (1 - a * b)) ^ 2 = 1 := by
            rw [show b = -1 by linarith [hb1]]
            have h1 : (1 + a : ℝ) ≠ 0 := by
              by_contra h2
              have h3 : a = -1 := by linarith
              have h4 : a * b = 1 := by
                rw [show a = -1 by linarith [h3]]
                rw [show b = -1 by linarith [hb1]]
                all_goals norm_num
              contradiction
            field_simp [h1]
            <;> nlinarith
          have eq2 : y ^ 2 = 1 := by
            rw [h_eq]
            linarith [eq1]
          exact eq2
    have eq1 : ((a - b) / (1 - a * b)) ^ 2 = 1 := h2 ((a - b) / (1 - a * b)) (by rfl)
    have h3 : abs ((a - b) / (1 - a * b)) = 1 := by
      have h4 : abs ((a - b) / (1 - a * b)) = Real.sqrt (((a - b) / (1 - a * b)) ^ 2) := by
        rw [Real.sqrt_sq_eq_abs]
      rw [h4]
      have h5 : Real.sqrt (((a - b) / (1 - a * b)) ^ 2) = 1 := by
        rw [eq1]
        all_goals norm_num
        <;> ring_nf <;> norm_num
      exact h5
    exact h3
  exact h1
  all_goals norm_num
  all_goals norm_num