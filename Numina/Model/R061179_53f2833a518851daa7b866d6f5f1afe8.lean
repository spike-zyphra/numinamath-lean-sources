import Mathlib

theorem number_theory_15861 : IsLeast {x : ℕ | 0 < x ∧ (20 - x) % 3 = 0} 2 := by 
  constructor 
  · -- Show that 2 is in the set {x : ℕ | 0 < x ∧ (20 - x) % 3 = 0}
    constructor 
    · norm_num
    · norm_num 
  · -- Show that if y ∈ {x : ℕ | 0 < x ∧ (20 - x) % 3 = 0} and y < 2, then y ≥ 2
    intro y 
    intro hy
    rcases hy with ⟨hy_pos, hy_div⟩
    by_contra h
    push_neg at h 
    -- Since y < 2 and y > 0, then y must be 1
    have h1 : y = 1 := by 
      omega 
    -- We can substitute y = 1 into the divisibility condition 
    -- So (20 - 1) % 3 = 19 % 3 should be 0 
    -- But 19 % 3 is 1, which contradicts (20 - y) % 3 = 0 
    rw [h1] at hy_div 
    norm_num at hy_div
    all_goals omega