import Mathlib

/- Arrange the products of every two of the five rational numbers $\frac{2}{3}$, $-\frac{5}{8}$, $\frac{15}{23}$, $-\frac{10}{17}$, $\frac{12}{19}$ in ascending order, then the smallest is ___          ___ , and the largest is ___          ___. -/
theorem algebra_1304 (a : Fin 5 → ℚ) (ha : a 0 = 2 / 3 ∧ a 1 = -5 / 8 ∧ a 2 = 15 / 23 ∧ a 3 = -10 / 17 ∧ a 4 = 12 / 19) :
    IsLeast {x | ∃ i j, i ≠ j ∧ x = a i * a j} (-5 / 12) ∧
    IsGreatest {x | ∃ i j, i ≠ j ∧ x = a i * a j} (10 / 23) := by

  rcases ha with ⟨ha0, ha1, ha2, ha3, ha4⟩

  constructor
  · -- First, we'll prove -5/12 is the least element in the set.
    constructor
    · -- First, we need to show -5/12 is indeed in the set.
      use 0, 1 
      all_goals
      simp [ha0, ha1]
      <;> norm_num
    · -- Now, we need to show that -5/12 is indeed the smallest.
      intro x hx 
      rcases hx with ⟨i, j, hineq, heq⟩ 
      fin_cases i <;> fin_cases j 
      <;> simp [heq, ha0, ha1, ha2, ha3, ha4] at *
      <;> norm_num at *
  · -- Now, we need to prove 10/23 is the greatest element in the set.
    constructor
    · -- First, we need to show 10/23 is indeed in the set.
      use 0, 2 
      all_goals 
      simp [ha0, ha2]
      <;> norm_num
    · -- Now, we need to show that 10/23 is indeed the largest.
      intro x hx 
      rcases hx with ⟨i, j, hineq, heq⟩ 
      fin_cases i <;> fin_cases j 
      <;> simp [heq, ha0, ha1, ha2, ha3, ha4] at *
      <;> norm_num at *