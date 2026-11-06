import Mathlib

/- ## Task 15/90

It is to be investigated whether the equation $3^{n}=10^{4} m+1$ with $m ; n \in N, m ; n>0$ has solutions! -/
theorem number_theory_161523 : ∃ n : ℕ, n > 0 ∧ ∃ m : ℕ, m > 0 ∧ 3^n = 10^4 * m + 1 := by
  -- provide n = 500 and m = floor(3^500 / 10000)
  use 500
  and_intros
  . positivity
  . use (3^500 / 10000)
    and_intros
    . positivity
    . have h100 : 3^500 % 10000 = 1 := by norm_num
      nth_rw 1 [← Nat.div_add_mod (3^500) 10000]
      rw [show 10^4 = 10000 by norm_num]
      rw [h100]