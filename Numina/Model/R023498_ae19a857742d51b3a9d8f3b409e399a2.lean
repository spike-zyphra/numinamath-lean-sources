import Mathlib

theorem inequalities_110571 (a b c : ℝ) :
    ¬(|a| < abs (b - c) ∧ |b| < abs (c - a) ∧ |c| < abs (a - b)) := by
  rintro ⟨h1, h2, h3⟩
  cases' abs_cases a with ha1 ha1 <;> 
    cases' abs_cases (b - c) with hb1 hb1 <;> 
      cases' abs_cases b with hb2 hb2 <;> 
        cases' abs_cases (c - a) with hc1 hc1 <;> 
          cases' abs_cases c with hc2 hc2 <;> 
            cases' abs_cases (a - b) with ha2 ha2 <;> 
              all_goals 
                linarith