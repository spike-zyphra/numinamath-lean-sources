import Mathlib

theorem number_theory_4082 :
    IsLeast {x : ℕ | ∃ y, 0 < x ∧ 0 < y ∧ x^2 - 3 * y^2 = 216} 18 := by
  constructor
  · -- Show 18 is in the set
    use 6
    all_goals norm_num
  · -- Show that no smaller element is in the set
    intro x hx
    rcases hx with ⟨y, hx1, hy1, heq⟩
    by_contra h
    push_neg at h
    have h1 : x ≤ 17 := by
      omega
    have h3 : y ≤ 4 := by
      by_contra h4
      push_neg at h4
      have h4 : y ≥ 5 := by
        omega
      have h7 : x ^ 2 ≥ 291 := by
        have h9 : x ^ 2 = 3 * y ^ 2 + 216 := by 
          omega
        have h10 : y ≥ 5 := h4
        nlinarith [h9, h10]
      have h8 : x ^ 2 ≤ 289 := by 
        nlinarith
      nlinarith
    interval_cases y <;> try { 
      have h2 : x ≤ 17 := by 
        omega
      interval_cases x <;> omega 
    }