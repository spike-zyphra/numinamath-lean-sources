import Mathlib

/-The length of the year on the planet Mars is exactly 697 days. If Mars has a calendar with a 12-day week, and year 0 begins on the first day of the week, what is the next year which will begin on the first day of the week?-/
theorem number_theory_23243 : IsLeast {n  > 0 | (n * 697) % 12 = 0} 12 := by
  -- Since $697 = 12 \cdot 58 + 1$, each Martian year consists of 58 weeks and a day.  
  -- Therefore, for every year that passes, the first day of the year shifts to the next day of the week.  Since year 0 begins on the first day, year 1 begins on the second day, then year 2 begins on the third day, and so on.  A week consists of 12 days, so the next year that begins on the first day again will be year $\boxed{12}$.
  have _12_in_set: 12 ∈ {n | 0 < n ∧ n * 697 % 12 = 0} := by simp
  unfold IsLeast
  use _12_in_set
  apply (le_csInf_iff' (Set.nonempty_of_mem _12_in_set)).mp
  apply le_csInf (Set.nonempty_of_mem _12_in_set)
  simp
  intro x hx₁ hx₂
  omega
