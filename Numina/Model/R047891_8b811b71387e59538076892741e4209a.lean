import Mathlib
open Mathlib
theorem algebra_94859 (a b c : ℝ) :
IsLeast {a | ∃ b c : ℝ, a > 0 ∧ (∀ x, a * (x - 1/4)^2 - 9/8 = a * x^2 + b * x + c) ∧ ∃ n : ℤ, a + b + c = n} (2 / 9) := by
  constructor
  · -- Show that 2/9 is indeed in the set 
    use -1 / 9, -10 / 9 
    constructor 
    · -- $a = 2/9 > 0$. 
      norm_num 
    constructor 
    · -- Show that for all $x$, $a(x - 1/4)^2 - 9/8 = ax^2 + Bx + c$. 
      intro x 
      ring_nf 
    · -- Check that $\frac{2}{9} + (-\frac{1}{9}) + (-\frac{10}{9}) = -1$ which is an integer. 
      use -1 
      all_goals norm_num 
  · -- Show that 2/9 is the minimum 
    intro a ha 
    rcases ha with ⟨b, c, ha_pos, heq, n, hneq⟩ 
    have eq1 := heq 0 
    have eq2 := heq 1 
    have eq3 := heq 2 
    norm_num at eq1 eq2 eq3 
    have eq4 : b = -a / 2 := by 
      nlinarith 
    have eq5 : c = a / 16 - 9 / 8 := by 
      nlinarith 
    have eq7 : (9 * a) / 16 - 9 / 8 = (n : ℝ) := by 
      have eq6 : a + b + c = (n : ℝ) := by 
        linarith 
      rw [eq4, eq5] at eq6 
      linarith 
    have hn1 : n ≥ -1 := by 
      by_contra h 
      push_neg at h 
      have hn2 : n ≤ -2 := by 
        omega 
      have eq8 : (n : ℝ) ≤ (-2 : ℝ) := by 
        exact_mod_cast hn2 
      nlinarith 
    have h6 : (n : ℝ) ≥ (-1 : ℝ) := by 
      exact_mod_cast hn1 
    nlinarith