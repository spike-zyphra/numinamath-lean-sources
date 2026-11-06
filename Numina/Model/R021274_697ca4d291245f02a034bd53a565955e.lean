import Mathlib

theorem number_theory_266233 :
    IsGreatest {x | ∃ p q : ℕ, p > 0 ∧ q > 0 ∧ p * q = 100 ∧ x = p + q} 101 := by
  constructor
  · -- Show 101 is in the set
    use 1, 100
    all_goals norm_num
  · -- Show that no greater element is in the set
    intro x hx
    rcases hx with ⟨p, q, hp, hq, hmul, heq⟩
    have h2 : p ≤ 100 := by
      by_contra h2
      push_neg at h2
      have h3 : p * q = 100 := hmul
      have h4 : p > 100 := h2
      have h5 : q < 1 := by
        nlinarith [h3, h4, hp]
      have h6 : q = 0 := by
        omega
      rw [h6] at hmul
      all_goals
        nlinarith
    have h2' : q ≤ 100 := by
      by_contra h2'
      push_neg at h2'
      have h3 : p * q = 100 := hmul
      have h4 : q > 100 := h2'
      have h5 : p < 1 := by
        nlinarith [h3, h4, hq]
      have h6 : p = 0 := by
        omega
      rw [h6] at hmul
      all_goals
        nlinarith
    have h6 : p ≤ 100 := h2
    have h7 : q ≤ 100 := h2'
    interval_cases p <;> omega