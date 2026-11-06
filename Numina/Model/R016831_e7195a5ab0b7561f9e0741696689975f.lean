import Mathlib

theorem algebra_314725 (a b c : ℝ) (h₀ : a + b + c = 0) (h₁ : a * b * c = 2) :
    abs a + abs b + abs c ≥ 4 := by 
  have h2 : ¬(a ≥ 0 ∧ b ≥ 0) := by
    intro h
    have ha : a ≥ 0 := h.1
    have hb : b ≥ 0 := h.2
    have hc : c ≤ 0 := by nlinarith
    have h3 : a * b * c ≤ 0 := by
      have h4 : a * b ≥ 0 := mul_nonneg ha hb
      nlinarith [show c ≤ 0 by linarith]
    nlinarith
  have h3 : ¬(b ≥ 0 ∧ c ≥ 0) := by
    intro h
    have hb : b ≥ 0 := h.1
    have hc : c ≥ 0 := h.2
    have ha : a ≤ 0 := by nlinarith
    have h4 : a * b * c ≤ 0 := by
      have h5 : b * c ≥ 0 := mul_nonneg hb hc
      nlinarith [show a ≤ 0 by linarith]
    nlinarith
  have h4 : ¬(a ≥ 0 ∧ c ≥ 0) := by
    intro h
    have ha : a ≥ 0 := h.1
    have hc : c ≥ 0 := h.2
    have hb : b ≤ 0 := by nlinarith
    have h5 : a * b * c ≤ 0 := by
      have h6 : a * c ≥ 0 := mul_nonneg ha hc
      nlinarith [show b ≤ 0 by linarith]
    nlinarith
  by_cases ha : a > 0
  · -- Assume a > 0 
    have hb1 : b ≤ 0 := by
      by_contra h
      push_neg at h
      have hb2 : b > 0 := by linarith
      have ha4 : a ≥ 0 := by linarith
      have hb4 : b ≥ 0 := by linarith
      -- Now we have a ≥ 0 ∧ b ≥ 0, which we already showed is a contradiction
      have h5 : a ≥ 0 ∧ b ≥ 0 := ⟨ha4, hb4⟩
      exfalso
      exact h2 h5
    have hc1 : c ≤ 0 := by
      by_contra h
      push_neg at h
      have hc2 : c > 0 := by linarith
      have ha4 : a ≥ 0 := by linarith
      have hc4 : c ≥ 0 := by linarith
      -- Now we have a ≥ 0 ∧ c ≥ 0, which we already showed is a contradiction
      have h7 : a ≥ 0 ∧ c ≥ 0 := ⟨ha4, hc4⟩
      exfalso
      exact h4 h7
    have h12 : abs a + abs b + abs c = a - b - c := by
      rw [abs_of_pos ha, abs_of_nonpos hb1, abs_of_nonpos hc1]
      all_goals
        ring
    rw [h12]
    have h6 : b + c = -a := by linarith
    have h7 : a - b - c = 2 * a := by
      nlinarith
    rw [h7]
    have h8 : a ≥ 2 := by
      nlinarith [sq_nonneg (b - c), sq_nonneg (a - 2), sq_nonneg (b + c + a), sq_nonneg (b * c - 1), sq_nonneg (a^2 - 4), sq_nonneg ((b + c) ^ 2 - 4 * (b * c)), mul_pos (show 0 < a by linarith) (show 0 < a by linarith)]
    nlinarith
  by_cases hb : b > 0
  · -- Assume b > 0 
    have ha1 : a ≤ 0 := by
      by_contra h
      push_neg at h
      have ha2 : a > 0 := by linarith
      have ha4 : a ≥ 0 := by linarith
      have hb4 : b ≥ 0 := by linarith
      have h5 : a ≥ 0 ∧ b ≥ 0 := ⟨ha4, hb4⟩
      exfalso
      exact h2 h5
    have hc1 : c ≤ 0 := by
      by_contra h
      push_neg at h
      have hc2 : c > 0 := by linarith
      have hb4 : b ≥ 0 := by linarith
      have hc4 : c ≥ 0 := by linarith
      have h7 : b ≥ 0 ∧ c ≥ 0 := ⟨hb4, hc4⟩
      exfalso
      exact h3 h7
    have h12 : abs a + abs b + abs c = -a + b - c := by
      rw [abs_of_nonpos ha1, abs_of_pos hb, abs_of_nonpos hc1]
      all_goals
        ring
    rw [h12]
    have h6 : a + c = -b := by linarith
    have h7 : -a + b - c = 2 * b := by
      nlinarith
    rw [h7]
    have h8 : b ≥ 2 := by
      nlinarith [sq_nonneg (a - c), sq_nonneg (b - 2), sq_nonneg (a + c + b), sq_nonneg (a * c - 1), sq_nonneg (b^2 - 4), sq_nonneg ((a + c) ^ 2 - 4 * (a * c)), mul_pos (show 0 < b by linarith) (show 0 < b by linarith)]
    nlinarith
  by_cases hc : c > 0
  · -- Assume c > 0 
    have ha1 : a ≤ 0 := by
      by_contra h
      push_neg at h
      have ha2 : a > 0 := by linarith
      have ha4 : a ≥ 0 := by linarith
      have hc4 : c ≥ 0 := by linarith
      have h7 : a ≥ 0 ∧ c ≥ 0 := ⟨ha4, hc4⟩
      exfalso
      exact h4 h7
    have hb1 : b ≤ 0 := by
      by_contra h
      push_neg at h
      have hb2 : b > 0 := by linarith
      have hb4 : b ≥ 0 := by linarith
      have hc4 : c ≥ 0 := by linarith
      have h7 : b ≥ 0 ∧ c ≥ 0 := ⟨hb4, hc4⟩
      exfalso
      exact h3 h7
    have h12 : abs a + abs b + abs c = -a - b + c := by
      rw [abs_of_nonpos ha1, abs_of_nonpos hb1, abs_of_pos hc]
      all_goals
        ring
    rw [h12]
    have h6 : a + b = -c := by linarith
    have h7 : -a - b + c = 2 * c := by
      nlinarith
    rw [h7]
    have h8 : c ≥ 2 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (c - 2), sq_nonneg (a + b + c), sq_nonneg (a * b - 1), sq_nonneg (c^2 - 4), sq_nonneg ((a + b) ^ 2 - 4 * (a * b)), mul_pos (show 0 < c by linarith) (show 0 < c by linarith)]
    nlinarith
  -- Now we know a ≤ 0, b ≤ 0, c ≤ 0
  have ha2 : a ≤ 0 := by nlinarith
  have hb2 : b ≤ 0 := by nlinarith
  have hc2 : c ≤ 0 := by nlinarith
  have h08 : a * b * c ≤ 0 := by
    have ha3 : a ≤ 0 := by linarith
    have hb3 : b ≤ 0 := by linarith
    have hc3 : c ≤ 0 := by linarith
    have h11 : a * b ≥ 0 := by
      apply mul_nonneg_of_nonpos_of_nonpos
      all_goals linarith
    have h10 : b * c ≥ 0 := by
      apply mul_nonneg_of_nonpos_of_nonpos
      all_goals linarith
    nlinarith [show c ≤ 0 by nlinarith]
  -- Now we see a contradiction
  nlinarith