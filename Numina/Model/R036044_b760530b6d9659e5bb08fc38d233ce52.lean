import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_219843 {f : ℝ → ℝ} (hf : f = λ x => abs (sin (2 * x)) + abs (cos (2 * x))) :
    IsLeast {x | 0 < x ∧ f = λ y => f (y + x)} (π/4) := by 
  constructor
  · -- Verify that π/4 is in the set.
    constructor
    · -- Show that π/4 > 0
      have h1 : π / 4 > 0 := by 
        linarith [Real.pi_pos]
      exact h1
    · -- Show that f = fun y ↦ f (y + π / 4)
      funext y
      have h2 : f y = f (y + π / 4) := by
        have h3 : sin (2 * (y + π / 4)) = cos (2 * y) := by 
          have h1 : 2 * (y + π / 4) = 2 * y + π / 2 := by ring
          rw [h1]
          rw [sin_add, sin_pi_div_two, cos_pi_div_two]
          ring
        have h4 : cos (2 * (y + π / 4)) = -sin (2 * y) := by
          have h2 : 2 * (y + π / 4) = 2 * y + π / 2 := by ring
          rw [h2]
          have h3 : cos (2 * y + π / 2) = -sin (2 * y) := by 
            rw [cos_add, cos_pi_div_two, sin_pi_div_two]
            ring
          exact h3
        have eq1 : f y = abs (sin (2 * y)) + abs (cos (2 * y)) := by
          rw [hf]
        have eq2 : f (y + π / 4) = abs (sin (2 * (y + π / 4))) + abs (cos (2 * (y + π / 4))) := by
          rw [hf]
        rw [eq1, eq2]
        have eq5 : abs (sin (2 * (y + π / 4))) = abs (cos (2 * y)) := by 
          rw [show sin (2 * (y + π / 4)) = cos (2 * y) by linarith [h3]]
        have eq6 : abs (cos (2 * (y + π / 4))) = abs (sin (2 * y)) := by 
          rw [show cos (2 * (y + π / 4)) = -sin (2 * y) by linarith [h4]]
          rw [abs_neg]
        rw [eq5, eq6]
        <;> ring_nf <;> try simp [abs_of_pos, abs_of_neg]
        all_goals try linarith
      exact h2
  · -- Show that π/4 is the smallest.
    intro x ⟨hx1, hx2⟩
    by_contra h
    push_neg at h
    have h3 := congr_fun hx2 (0)
    simp [hf] at h3
    have h4 : 0 < 2 * x := by linarith
    have h5 : 2 * x < π / 2 := by
      linarith [Real.pi_pos, h]
    have h6 : sin (2 * x) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith
      linarith
    have h7 : cos (2 * x) > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      linarith
      linarith
    have h8 : abs (sin (2 * x)) = sin (2 * x) := by 
      rw [abs_of_pos h6]
    have h9 : abs (cos (2 * x)) = cos (2 * x) := by 
      rw [abs_of_pos h7]
    rw [h8, h9] at h3
    nlinarith [Real.sin_pos_of_pos_of_lt_pi (show 0 < 2 * x by linarith) (show 2 * x < Real.pi by linarith [Real.pi_gt_three, h5]), Real.sin_sq_add_cos_sq (2 * x), sq_nonneg (sin (2 * x) - 0), sq_nonneg (cos (2 * x) - 0), sq_nonneg (sin (2 * x) + cos (2 * x) - 1)]