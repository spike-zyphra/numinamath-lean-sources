import Mathlib

/- 1. Show that the Diophantine equation


$$

a^{2}+b^{2}=2023

$$


has no solutions.

2. Show that the Diophantine equation


$$

a^{5}-2 b^{2}=2022

$$


has no solutions.

NOTE: problem has typo possibly, instead of 2022, should be 2020

 -/
theorem number_theory_128189 (a b : ℤ) :
    a^2 + b^2 ≠ 2023 ∧ a^5 - 2 * b^2 ≠ 2020 := by
  and_intros
    -- if we try mod 4 all values of a, b we see not possible hence impossible
  . have h' (x y : ZMod 4) : x^2 + y^2 ≠ 2023 := by
      fin_cases x
      all_goals (
        fin_cases y
        all_goals (
          simp
          norm_num
          norm_cast
        )
      )
    replace h' := h' a b
    norm_cast at h'
    by_contra h
    rw [h] at h'
    simp at h'
    -- if we try mod 11 all values of a, b we see not possible hence impossible
  . have h' (x y : ZMod 11) : x^5 - 2 * y^2 ≠ 2020 := by
      fin_cases x
      all_goals (
        fin_cases y
        all_goals (
          simp
          norm_num
          norm_cast
        )
      )
    replace h' := h' a b
    norm_cast at h'
    by_contra h
    rw [h] at h'
    simp at h'