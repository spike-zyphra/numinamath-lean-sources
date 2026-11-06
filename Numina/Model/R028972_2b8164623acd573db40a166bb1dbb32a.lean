import Mathlib

theorem number_theory_269192 (n : ℕ) (hn : n = 126) :
    IsGreatest {x | ∃ p q, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p + q = n ∧ x = p - q} 100 := by 
  rw [hn]
  constructor
  · -- Show 100 is in the set
    use 113, 13
    all_goals
      norm_num 
  · -- Show that 100 is greatest in the set
    intro x hx
    rcases hx with ⟨p, q, hp, hq, hneq, hsum, hx⟩
    by_contra h
    push_neg at h
    have h1 : p ≤ 126 := by
      linarith
    have h2 : q = 126 - p := by
      omega
    have h3 : p > 113 := by
      by_contra h5
      push_neg at h5
      have h4 : p ≤ 113 := by
        omega
      have h10 : q ≥ 13 := by
        omega
      have h11 : p ≤ 113 := by
        omega
      interval_cases p <;> norm_num [h2] at hq hp hx hsum hneq ⊢
      <;> omega 
    have h4 : p ≤ 126 := by
      linarith
    interval_cases p <;> norm_num [h2] at hq hp hx hsum hneq ⊢
    <;> omega