import Mathlib

theorem algebra_198587 (c : ℝ) :
    IsLeast {c | ∃! x : ℝ, ∃! y : ℝ, 2 * (x + 7) ^ 2 + (y - 4) ^ 2 = c ∧ (x + 4) ^ 2 + 2 * (y - 7) ^ 2 = c} 6 := by 
  constructor
  · -- Show that 6 is in the set 
    use -6 
    constructor
    · -- Show that for x = -6, there is a unique y 
      use 6 
      constructor 
      · -- Verify that (-6, 6) satisfies both equations with c = 6 
        norm_num 
      · -- Show that for x = -6, y = 6 is the only possible solution 
        intro y hy 
        rcases hy with ⟨h_eq1, h_eq2⟩ 
        nlinarith [sq_nonneg (y - 6)]
    · -- Show that for any x with the property, -6 = x 
      intro x ⟨y, ⟨h_eq1, h_eq2⟩, hy⟩ 
      have h3 : (x + y) * (x - y + 20) = 0 := by 
        nlinarith 
      have h4 : x + y = 0 ∨ x - y + 20 = 0 := by 
        cases (mul_eq_zero.mp h3) with 
        | inl h5 => 
          left 
          linarith 
        | inr h6 => 
          right 
          linarith 
      cases h4 with 
      | inl h5 => 
        have h6 : y = -x := by linarith 
        have h_eq1' := h_eq1 
        rw [h6] at h_eq1 
        have h_eq2' := h_eq2 
        rw [h6] at h_eq2 
        have : x = -6 := by 
          nlinarith 
        linarith 
      | inr h7 => 
        -- This case is impossible as it would require c=54
        have h8 : y = x + 20 := by linarith 
        rw [h8] at h_eq1 h_eq2 
        nlinarith [sq_nonneg (x + 10)]
  · -- Show that 6 is minimal 
    intro c hc 
    rcases hc with ⟨x, ⟨y, ⟨h_eq1, h_eq2⟩, hy⟩, hx⟩ 
    have h3 : (x + y) * (x - y + 20) = 0 := by 
      nlinarith 
    have h4 : x + y = 0 ∨ x - y + 20 = 0 := by 
      cases (mul_eq_zero.mp h3) with 
      | inl h5 => 
        left 
        linarith 
      | inr h6 => 
        right 
        linarith 
    cases h4 with 
    | inl h5 => 
      -- Case where x + y = 0, so y = -x 
      have h6 : y = -x := by linarith 
      have h_eq1' := h_eq1 
      rw [h6] at h_eq1 
      have h_eq2' := h_eq2 
      rw [h6] at h_eq2 
      nlinarith [sq_nonneg (x + 6)]
    | inr h7 => 
      -- Case where x - y + 20 = 0, so y = x + 20 
      have h8 : y = x + 20 := by linarith 
      have h_eq1' := h_eq1 
      rw [h8] at h_eq1 
      have h_eq2' := h_eq2 
      rw [h8] at h_eq2 
      nlinarith [sq_nonneg (x + 10)]