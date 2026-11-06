import Mathlib

theorem algebra_21153 :
    IsLeast {x | ∃ a b : ℕ, a ≠ b ∧ a > 0 ∧ b > 0 ∧ a ∣ 80 ∧ b ∣ 80 ∧ a * b = x ∧ ¬(x ∣ 80)} 32 := by 
  constructor
  · -- Show that 32 is in the set 
    use 4, 8 
    all_goals norm_num 
  · -- Show that no smaller element is in the set
    intro x hx 
    rcases hx with ⟨a, b, hne, ha_pos, hb_pos, ha, hb, heq, hn⟩ 
    by_contra h
    push_neg at h 
    -- From h: we have x < 32
    have h1 : a * b < 32 := by 
      nlinarith 
    have h2 : a ∣ 80 := ha 
    have h3 : b ∣ 80 := hb 
    have h4 : a ≤ 31 := by 
      by_contra h4 
      push_neg at h4 
      have h5 : a * b ≥ 32 := by 
        have h6 : b ≥ 1 := by linarith 
        nlinarith 
      omega 
    have h5 : b ≤ 31 := by 
      by_contra h5 
      push_neg at h5 
      have h6 : a * b ≥ 32 := by 
        have  h7 : a ≥ 1 := by linarith 
        nlinarith 
      omega 
    have h6 : x ∣ 80 := by 
      have h8 : x = a * b := by linarith 
      rw [h8] 
      have h9 : a ∣ 80 := h2 
      have h10 : b ∣ 80 := h3 
      have h99 : a ≤ 31 := h4 
      have h100 : b ≤ 31 := h5 
      interval_cases a <;> norm_num at h9 h99 ⊢ 
      <;> try { 
        omega 
      }
      <;> try { 
        interval_cases b 
        <;> norm_num at h10 h100 ⊢ 
        <;> try { 
          omega 
        }
      }
    -- This contradicts hn: ¬(x ∣ 80)
    contradiction