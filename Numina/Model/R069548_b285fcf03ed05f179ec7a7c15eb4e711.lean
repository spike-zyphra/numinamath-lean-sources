import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_53098 (l : ℝ) (hl : l > 0) :
    ¬ (∀ vmax : ℝ, vmax > 0 → l / vmax > π / 2) := by 
  intro h
  have h1 := h (2 * l / π) (by
    -- show that $2 * l / π > 0$
    have hpi : π > 0 := by
      exact pi_pos
    positivity
  )
  have h2 : l / (2 * l / π) > π / 2 := h1
  -- simplify the left side of h2
  have h3 : l / (2 * l / π) = π / 2 := by
    field_simp
    <;> ring_nf <;> field_simp <;> linarith [pi_pos, pi_gt_three]
  -- derive contradiction
  nlinarith [pi_pos, pi_gt_three]