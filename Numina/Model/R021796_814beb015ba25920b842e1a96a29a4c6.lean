import Mathlib

open Real Set

/- For all real numbers $x, y$ satisfying $|x|+|y|\leqslant 1$, the inequality $|2x-3y+\frac{3}{2}|+|y-1|+|2y-x-3|\leqslant a$ always holds, then the minimum value of the real number $a$ is ___          ___. -/
theorem inequalities_11830 (a : ℝ) :
    (∀ x y : ℝ, |x| + |y| ≤ 1 → |2 * x - 3 * y + 3 / 2| + |y - 1| + |2 * y - x - 3| ≤ a) ↔
    a ≥ 23 / 2 := by
  constructor
  · -- Assume the inequality holds for all x, y with |x| + |y| ≤ 1, prove a ≥ 23/2
    intro h
    have h1 := h 0 (-1) (by
      norm_num [abs_le]
    )
    norm_num [abs] at h1 ⊢
    linarith
  · -- Assume a ≥ 23/2, prove the inequality for all x,y with |x| + |y| ≤ 1
    intro ha x y h
    have h1 : |x| + |y| ≤ 1 := h
    cases' abs_cases x with hx hx <;> cases' abs_cases y with hy hy <;> 
      cases' abs_cases (2 * x - 3 * y + 3 / 2) with h1 h1 <;> 
        cases' abs_cases (y - 1) with h2 h2 <;> 
          cases' abs_cases (2 * y - x - 3) with h3 h3 <;> 
            all_goals 
              linarith