import Mathlib

theorem algebra_10760 :
    IsGreatest {x | ∃ a b : ℕ, 69 * a + 54 * b ≤ 2008 ∧ x = a * b} 270 := by
  constructor
  · -- Show that 270 is in the set
    use 15, 18
    all_goals norm_num
  · -- Show that 270 is greatest
    intro x hx
    rcases hx with ⟨a, b, h1, h2⟩
    have h4 : a ≤ 29 := by
      by_contra h
      push_neg at h
      have h5 : a ≥ 30 := by omega
      have h6 : 69 * a ≥ 2070 := by 
        nlinarith
      omega
    have h5 : b ≤ 37 := by
      by_contra h
      push_neg at h
      have h7 : b ≥ 38 := by omega
      have h8 : 54 * b ≥ 1992 := by 
        nlinarith
      omega
    have h6 : a * b ≤ 270 := by
      interval_cases a <;> try { 
        omega 
      }
      <;> try { 
        interval_cases b 
        <;> omega 
      }
    have h7 : x ≤ 270 := by
      nlinarith
    linarith