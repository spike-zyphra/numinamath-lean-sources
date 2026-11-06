import Mathlib

theorem inequalities_189838 (x y z : ℝ) :
    (|x| < |y - z| ∧ |y| < |z - x| ∧ |z| < |x - y|) ↔ False := by 
  constructor
  · -- Assume the conjunction of the three inequalities holds, prove False
    rintro ⟨h1, h2, h3⟩
    have h11 : |x| < |y - z| := h1
    have h12 : |y| < |z - x| := h2
    have h13 : |z| < |x - y| := h3
    have h21 : x ^ 2 < (y - z) ^ 2 := by
      apply sq_lt_sq.mpr
      exact h11
    have h22 : y ^ 2 < (z - x) ^ 2 := by
      apply sq_lt_sq.mpr
      exact h12
    have h23 : z ^ 2 < (x - y) ^ 2 := by
      apply sq_lt_sq.mpr
      exact h13
    cases' abs_cases x with hx hx <;> cases' abs_cases (y - z) with h2 h2 <;> cases' abs_cases y with hy hy <;> cases' abs_cases (z - x) with h4 h4 <;> cases' abs_cases z with hz hz <;> cases' abs_cases (x - y) with h5 h5 <;> 
      all_goals 
        linarith
  · -- Assume False, prove the conjunction...
    intro h
    have h1 : |x| < |y - z| := by 
      exfalso
      exact h
    have h2 : |y| < |z - x| := by 
      exfalso
      exact h
    have h3 : |z| < |x - y| := by 
      exfalso
      exact h
    exact ⟨h1, h2, h3⟩