import Mathlib


theorem number_theory_290855 :
    IsGreatest {x | ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ |(p : ℤ) - q| = 2 ∧ p ≤ 200 ∧ q ≤ 200 ∧ x = p + q} 396 := by
  constructor
  · -- Show 396 is in the set
    use 197, 199
    all_goals
      norm_num
  · -- Show that 396 is greatest
    intro x hx
    rcases hx with ⟨p, q, hp, hq, h1, hp200, hq200, hx⟩
    have h2 : (p : ℤ) ≤ 200 := by omega
    have h3 : (q : ℤ) ≤ 200 := by omega
    cases' eq_or_eq_neg_of_abs_eq h1 with h6 h7
    · -- Case where p - q = 2, so p = q + 2
      have h8 : (p : ℤ) = q + 2 := by linarith
      have h9 : p = q + 2 := by
        omega
      by_contra h
      push_neg at h
      have h10 : p + q > 396 := by linarith
      have h11 : q > 197 := by
        omega
      have h12 : q ≤ 198 := by
        omega
      have h13 : q = 198 := by
        omega
      have h14 : p = 200 := by
        omega
      have h15 : ¬p.Prime := by
        rw [h14]
        norm_num
      contradiction
    · -- Case where q - p = 2, so q = p + 2
      have h8 : (q : ℤ) = p + 2 := by linarith
      have h9 : q = p + 2 := by
        omega
      by_contra h
      push_neg at h
      have h10 : p + q > 396 := by linarith
      have h11 : p > 197 := by
        omega
      have h12 : p ≤ 198 := by
        omega
      have h13 : p = 198 := by
        omega
      have h14 : q = 200 := by
        omega
      have h15 : ¬q.Prime := by
        rw [h14]
        norm_num
      contradiction