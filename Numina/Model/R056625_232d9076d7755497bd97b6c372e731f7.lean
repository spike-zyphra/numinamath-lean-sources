import Mathlib

theorem inequalities_174554 (x : ℕ) :
    (11 / 15 : ℝ) < (7 / x : ℝ) ∧ (7 / x : ℝ) < (15 / 11 : ℝ) ↔
    x = 6 ∨ x = 7 ∨ x = 8 ∨ x = 9 := by
  constructor
  · -- Forward direction: If the inequality holds, then x is in the set
    intro h
    rcases h with ⟨h₁, h₂⟩
    -- Show that x > 0
    have hx1 : x > 0 := by
      by_contra h'
      push_neg at h'
      have h'1 : x = 0 := by omega
      rw [h'1] at h₁ h₂
      norm_num at h₁ h₂
    -- From left inequality: 11/15 < 7/x
    have h3 : x ≤ 9 := by
      by_contra h'
      push_neg at h'
      have hx2 : (x : ℝ) > 0 := by exact_mod_cast (show x > 0 by linarith)
      have h4 : (x : ℝ) ≥ (10 : ℝ) := by
        have h5 : x ≥ 10 := by omega
        exact_mod_cast h5
      -- Show contradiction
      have h6 : (11 / 15 : ℝ) < (7 / (x : ℝ)) := h₁
      have h7 : (x : ℝ) ≥ (10 : ℝ) := by linarith
      -- Multiply both sides by 15 * x
      have h8 : (11 : ℝ) * (x : ℝ) < (105 : ℝ) := by
        have h9 : (7 / (x : ℝ) : ℝ) > (11 / 15 : ℝ) := by linarith
        have h10 : (x : ℝ) > (0 : ℝ) := by nlinarith [h9]
        have h11 : (7 / (x : ℝ) : ℝ) = (7 : ℝ) / (x : ℝ) := by ring
        have h12 : (11 / 15 : ℝ) = (11 : ℝ) / 15 := by ring
        rw [h11, h12] at h9
        apply (div_lt_div_iff (by positivity) (by positivity)).mp at h9
        nlinarith
      nlinarith
    -- From right inequality: 7/x < 15/11
    have h5 : x ≥ 6 := by
      by_contra h'
      push_neg at h'
      have hx3 : x ≤ 5 := by omega
      interval_cases x <;> norm_num at h₁ h₂ <;> try { contradiction }
      <;> norm_num at h₁ h₂ <;> tauto
    -- Combine the inequalities
    have h8 : x = 6 ∨ x = 7 ∨ x = 8 ∨ x = 9 := by
      omega
    exact h8
  · -- Reverse direction: If x is in the set, then the inequality holds
    rintro (rfl | rfl | rfl | rfl)
    · constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num
      · norm_num