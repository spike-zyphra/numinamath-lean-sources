import Mathlib

theorem number_theory_150750 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hdist : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    IsLeast {x | ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ x = a * b * c / (a + b + c)} 1 := by
  constructor
  · -- Show that 1 is in the set 
    use 1, 2, 3
    all_goals
      norm_num
  · -- Show that 1 is minimal 
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, hab, hac, hbc, hx⟩
    by_contra h 
    push_neg at h 
    have h6 : x = 0 := by 
      omega 
    rw [h6] at hx 
    exfalso 
    -- Show that a * b * c ≥ a + b + c for distinct positive natural numbers a, b, c. 
    have h7 : a * b * c < a + b + c := by 
      by_contra h 
      push_neg at h 
      have h8 : (a * b * c) / (a + b + c) > 0 := by 
        apply Nat.div_pos 
        all_goals linarith 
      omega 
    have h8 : a * b * c ≥ a + b + c := by 
      have h12 : a ≥ 1 := by linarith 
      have h13 : b ≥ 1 := by linarith 
      have h14 : c ≥ 1 := by linarith 
      have h6 : a ≠ b := hab 
      have h7 : a ≠ c := hac 
      have h8 : b ≠ c := hbc 
      have h9 : a * b * c ≥ a + b + c := by 
        have h10 : a ≥ 1 := h12 
        have h11 : b ≥ 1 := h13 
        have h12 : c ≥ 1 := h14 
        by_contra h 
        push_neg at h 
        have h10 : a ≤ 3 := by 
          by_contra h11 
          push_neg at h11 
          have h12 : b ≤ 3 := by 
            nlinarith [show a * b * c < a + b + c by linarith, mul_pos (show 0 < a by linarith) (show 0 < b by linarith), mul_pos (show 0 < a by linarith) (show 0 < c by linarith), mul_pos (show 0 < b by linarith) (show 0 < c by linarith)]
          have h13 : c ≤ 3 := by 
            nlinarith [show a * b * c < a + b + c by linarith, mul_pos (show 0 < a by linarith) (show 0 < b by linarith), mul_pos (show 0 < a by linarith) (show 0 < c by linarith), mul_pos (show 0 < b by linarith) (show 0 < c by linarith)]
          interval_cases b <;> interval_cases c 
          <;> omega 
        have h11 : b ≤ 3 := by 
          by_contra h12 
          push_neg at h12 
          have h13 : a ≤ 3 := by 
            nlinarith [show a * b * c < a + b + c by linarith, mul_pos (show 0 < a by linarith) (show 0 < b by linarith), mul_pos (show 0 < a by linarith) (show 0 < c by linarith), mul_pos (show 0 < b by linarith) (show 0 < c by linarith)]
          have h14 : c ≤ 3 := by 
            nlinarith [show a * b * c < a + b + c by linarith, mul_pos (show 0 < a by linarith) (show 0 < b by linarith), mul_pos (show 0 < a by linarith) (show 0 < c by linarith), mul_pos (show 0 < b by linarith) (show 0 < c by linarith)]
          interval_cases a <;> interval_cases c 
          <;> omega 
        have h12 : c ≤ 3 := by 
          by_contra h13 
          push_neg at h13 
          have h14 : a ≤ 3 := by 
            nlinarith [show a * b * c < a + b + c by linarith, mul_pos (show 0 < a by linarith) (show 0 < b by linarith), mul_pos (show 0 < a by linarith) (show 0 < c by linarith), mul_pos (show 0 < b by linarith) (show 0 < c by linarith)]
          have h15 : b ≤ 3 := by 
            nlinarith [show a * b * c < a + b + c by linarith, mul_pos (show 0 < a by linarith) (show 0 < b by linarith), mul_pos (show 0 < a by linarith) (show 0 < c by linarith), mul_pos (show 0 < b by linarith) (show 0 < c by linarith)]
          interval_cases a <;> interval_cases b 
          <;> omega 
        interval_cases a <;> interval_cases b <;> interval_cases c 
        <;> norm_num at h 
        <;> norm_num at h6 h7 h8 
        all_goals omega 
      linarith 
    linarith