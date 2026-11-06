import Mathlib
set_option maxRecDepth 2000

theorem number_theory_300799 : IsGreatest { l | ∃ m n, l = m.lcm n ∧ m ≠ n ∧
    m + n = 2012} (1005 * 1007) := by 
  constructor 
  · -- Show 1005 * 1007 is in the set 
    use 1005, 1007 
    all_goals 
      norm_num 
  · -- Show there is no greater element in the set 
    intro l hl 
    rcases hl with ⟨m, n, h1, h2, h3⟩ 
    have h4 : n = 2012 - m := by 
      omega 
    rw [show n = 2012 - m by omega] at h1 
    by_contra h 
    push_neg at h 
    have h5 : m ≤ 2012 := by 
      omega 
    interval_cases m <;> norm_num [h1] at h ⊢ 
      <;> omega