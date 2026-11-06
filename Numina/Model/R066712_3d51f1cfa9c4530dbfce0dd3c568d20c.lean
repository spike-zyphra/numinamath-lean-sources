import Mathlib

/- Given that $n$ is a multiple of $2014$ and greater than $2014$, and its last two digits are $14$, then the minimum value of $n$ is ___          ___. -/
theorem number_theory_7320 :
    IsLeast {n | 2014 ∣ n ∧ n > 2014 ∧ (n % 100) = 14} 102714 := by 
  constructor
  · -- Show that 102714 satisfies all conditions
    constructor
    · -- prove 2014 | 102714
      norm_num
    constructor
    · -- 102714 > 2014
      norm_num
    · -- 102714 % 100 = 14
      norm_num
  · -- Show that 102714 is the least
    intro n hn
    rcases hn with ⟨hdiv, h1, h2⟩
    omega