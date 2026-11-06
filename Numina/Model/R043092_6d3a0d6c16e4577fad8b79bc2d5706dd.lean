import Mathlib

open Real Set
open scoped Real

theorem calculus_22506 : cos (π / 5) = (1 + sqrt 5) / 4 := by
  have h1 : cos (π / 5) = (1 + sqrt 5) / 4 := by
    have h2 : cos (π / 5) = (1 + sqrt 5) / 4 := by
      rw [cos_pi_div_five]
      all_goals
        ring_nf
        <;> field_simp
        <;> norm_num
    exact h2
  exact h1