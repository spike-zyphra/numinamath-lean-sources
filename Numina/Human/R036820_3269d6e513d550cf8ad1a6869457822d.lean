import Mathlib

/- The integers $x$, $y$ satisfy the equation $2xy + x + y = 83$, then $x + y = $ __          __ or __          ___ -/
theorem algebra_625467 {x y : ℤ} (h : 2*x*y + x + y = 83) :
    x + y = 83 ∨ x + y = -85 := by
        have h1 : (x + y = 83) ∨ (x + y = -85) := by
            by_cases h2 : x ≤ y
            · -- Assume x ≤ y
              by_cases h3 : x ≥ 0
              · -- x ≥ 0
                by_cases h4 : y ≥ 0
                · -- Both x, y ≥ 0
                  have h4' : x ≤ 42 := by nlinarith [sq_nonneg (x - 42), sq_nonneg (y - 42), h]
                  interval_cases x <;> omega
                · -- y < 0
                  linarith
              · -- x < 0
                by_cases h4 : y ≥ 0
                · -- x < 0, y ≥ 0
                  have h4' : x ≥ -84 := by nlinarith [sq_nonneg (x + 84), sq_nonneg (y - 84), h]
                  interval_cases x <;> omega
                · -- Both x, y < 0
                  have h4' : x ≥ -84 := by nlinarith [sq_nonneg (x + 84), sq_nonneg (y + 42), h]
                  interval_cases x <;> omega
            · -- Assume y < x
              by_cases h3 : y ≥ 0
              · -- y ≥ 0
                by_cases h4 : x ≥ 0
                · -- Both x, y ≥ 0
                  have h4' : y ≤ 42 := by nlinarith [sq_nonneg (x - 42), sq_nonneg (y - 42), h]
                  interval_cases y <;> omega
                · -- x < 0, y ≥ 0
                  nlinarith [sq_nonneg (x + 42), sq_nonneg (y - 84), h]
              · -- y < 0
                by_cases h4 : x ≥ 0
                · -- x ≥ 0, y < 0
                  have h4' : y ≥ -84 := by nlinarith [sq_nonneg (x - 84), sq_nonneg (y + 84), h]
                  interval_cases y <;> omega
                · -- Both x, y < 0
                  have h4' : y ≥ -84 := by nlinarith [sq_nonneg (x + 42), sq_nonneg (y + 84), h]
                  interval_cases y <;> omega
        exact h1
