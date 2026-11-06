import Mathlib

theorem inequalities_223947 (x y z : ℝ) :
    ¬(|x| < |y - z| ∧ |y| < |z - x| ∧ |z| < |x - y|) := by 
  intro h
  rcases h with ⟨h1, h2, h3⟩
  cases' abs_cases x with hx hx <;> 
    cases' abs_cases (y - z) with h11 h11 <;> 
      cases' abs_cases y with hy hy <;> 
        cases' abs_cases (z - x) with h22 h22 <;> 
          cases' abs_cases z with hz hz <;> 
            cases' abs_cases (x - y) with h33 h33 <;> 
              linarith