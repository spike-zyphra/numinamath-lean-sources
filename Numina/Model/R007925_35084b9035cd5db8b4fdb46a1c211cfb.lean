import Mathlib

theorem number_theory_199282 : IsLeast {a : ℕ | 0 < a ∧ 18305 ∣ (a + 1)^5 - a^5 - 1} 60 := by 
  constructor 
  · constructor 
    · norm_num 
    · norm_num 
  · intro a ha 
    rcases ha with ⟨ha_pos, ha_div⟩ 
    by_contra h 
    push_neg at h 
    interval_cases a <;> norm_num at ha_div ⊢ <;> all_goals omega