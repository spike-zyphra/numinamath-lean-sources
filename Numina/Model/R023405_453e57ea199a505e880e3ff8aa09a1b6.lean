import Mathlib

theorem number_theory_286587 (x y : ℕ) (hx : x > 0) (hy : y > 0)
    (h : 1 + x + y + x * y = 2008) :
    (x = 1 ∧ y = 1003) ∨ (x = 1003 ∧ y = 1) ∨ (x = 3 ∧ y = 501) ∨
    (x = 501 ∧ y = 3) ∨ (x = 7 ∧ y = 250) ∨ (x = 250 ∧ y = 7) := by
  have h1 : (x + 1) * (y + 1) = 2008 := by 
    nlinarith
  have h2 : x ≤ 2007 := by
    by_contra h2
    push_neg at h2
    have h3 : x + 1 ≥ 2009 := by 
      omega
    have h4 : (x + 1) * (y + 1) ≥ 2009 * 1 := by
      have h5 : y + 1 ≥ 1 := by 
        omega
      nlinarith
    nlinarith
  have h3 : y ≤ 2007 := by
    by_contra h3
    push_neg at h3
    have h4 : y + 1 ≥ 2009 := by 
      omega
    have h5 : (x + 1) * (y + 1) ≥ 1 * 2009 := by
      have h6 : x + 1 ≥ 1 := by 
        omega
      nlinarith
    nlinarith
  interval_cases x <;> omega