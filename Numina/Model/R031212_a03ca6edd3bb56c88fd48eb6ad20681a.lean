import Mathlib

theorem algebra_253081 {x y : ℝ} (hx : x + y = 6) (hy : y > 0)
    (h : y ^ (x ^ 2 + 7 * x + 12) = 1) :
    (x = 5 ∧ y = 1) ∨ (x = -3 ∧ y = 9) ∨ (x = -4 ∧ y = 10) := by
  have h1 : y = 6 - x := by linarith
  rw [h1] at h
  have h4 : (6 - x : ℝ) > 0 := by nlinarith [hy, h1]
  have h5 : (6 - x : ℝ) ^ (x ^ 2 + 7 * x + 12) = 1 := h
  have h6 : (6 - x = 1) ∨ (x ^ 2 + 7 * x + 12 = (0 : ℝ)) := by
    by_cases h7 : (6 - x : ℝ) = 1
    · -- If $6 - x = 1$, then $x = 5$
      left
      linarith
    · -- Assume $6 - x \neq 1$
      have h7 : (6 - x : ℝ) ≠ 1 := by exact h7
      have h8 : (x ^ 2 + 7 * x + 12 : ℝ) = 0 := by
        by_cases h9 : (x ^ 2 + 7 * x + 12 : ℝ) = 0
        · -- Case $x ^ 2 + 7 * x + 12 = 0$
          exact h9
        · -- Assume $x^2 + 7 x + 12 \neq 0$
          have h10 : (x ^ 2 + 7 * x + 12 : ℝ) ≠ 0 := by exact h9
          have h11 : (6 - x : ℝ) ^ (x ^ 2 + 7 * x + 12) = 1 := h5
          have h13 : (x ^ 2 + 7 * x + 12 : ℝ) * (Real.log (6 - x : ℝ)) = 0 := by
            calc
              (x ^ 2 + 7 * x + 12 : ℝ) * (Real.log (6 - x : ℝ))
                  = Real.log ((6 - x : ℝ) ^ (x ^ 2 + 7 * x + 12)) := by
                    rw [Real.log_rpow]
                    all_goals linarith
              _ = Real.log (1) := by
                rw [h11]
              _ = (0 : ℝ) := by
                norm_num
          cases' (mul_eq_zero.mp h13) with h14 h15
          · -- Case $x^2 + 7x + 12 = 0$
            exact h14
          · -- Case Real.log (6 - x) = 0
            have h16 : (6 - x : ℝ) = 1 := by
              have h17 : Real.log (6 - x : ℝ) = 0 := by
                linarith
              rw [Real.log_eq_zero] at h17
              rcases h17 with (r | r | r)
              · -- Case $6 - x = 1$
                linarith
              · -- Case $6 - x = 1$
                linarith
              · -- Case $6 - x = 1$
                linarith
            have h17 : (6 - x : ℝ) = 1 := h16
            have h18 : (6 - x : ℝ) = 1 := h17
            contradiction
      right
      linarith
  cases' h6 with h61 h62
  · -- Case $6 - x = 1$, so $x = 5$, $y = 1$
    have hx1 : x = 5 := by linarith
    have hy1 : (6 - x : ℝ) = 1 := by linarith
    left
    have hy1' : y = 1 := by
      nlinarith [h1, hx1]
    exact ⟨hx1, hy1'⟩
  · -- Case $x^2 + 7 x + 12 = 0$, so $x = -3$ or $x = -4$
    have h10 : x ^ 2 + 7 * x + 12 = (0 : ℝ) := by
      linarith
    have h11 : (x + 3) * (x + 4) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h11) with h12 h13
    · -- Case $x + 3 = 0$, so $x = -3$, $y = 9$
      have hx2 : x = -3 := by linarith
      have hy2 : y = 9 := by
        nlinarith [h1, hx2]
      right
      left
      exact ⟨hx2, hy2⟩
    · -- Case $x + 4 = 0$, so $x = -4$, $y = 10$
      have hx3 : x = -4 := by linarith
      have hy3 : y = 10 := by
        nlinarith [h1, hx3]
      right
      right
      exact ⟨hx3, hy3⟩