import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_111385 {f : ℝ → ℝ} (hf : f = λ x => abs (sin x) + abs (cos x)) :
    IsLeast {T | 0 < T ∧ f = λ x => f (x + T)} (π / 2) := by
  constructor
  · -- Show π/2 is in the set
    constructor
    · -- Show π/2 > 0
      positivity
    · -- Show f = fun x, f (x + π / 2)
      funext x
      have h1 : f x = abs (sin x) + abs (cos x) := by
        simp [hf]
      have h2 : f (x + π / 2) = abs (sin (x + π / 2)) + abs (cos (x + π / 2)) := by
        simp [hf]
      rw [h1, h2]
      have h3 : sin (x + π / 2) = cos x := by
        rw [sin_add, sin_pi_div_two, cos_pi_div_two]
        ring
      have h4 : cos (x + π / 2) = - sin x := by
        rw [cos_add, sin_pi_div_two, cos_pi_div_two]
        ring
      rw [h3, h4]
      have h6 : abs (- sin x) = abs (sin x) := by
        simp [abs_neg]
      rw [h6]
      all_goals
        ring
  · -- Show π/2 is the smallest
    intro T ⟨hT_pos, hfT⟩
    have h1 : ∀ x, f x = f (x + T) := by
      intro x
      simpa using congr_fun hfT x
    have eq1 := h1 0
    simp [hf] at eq1
    by_contra h
    push_neg at h
    have h2 : sin T > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      · -- Show 0 < T
        linarith [hT_pos]
      · -- Show T < Real.pi
        have hT_lt_pi : T < Real.pi := by
          nlinarith [h, Real.pi_gt_31415, Real.pi_lt_31416, Real.pi_pos]
        linarith
    have h3 : cos T > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      · -- Show -pi/2 < T
        nlinarith [Real.pi_pos, hT_pos]
      · -- Show T < pi/2
        nlinarith [h, Real.pi_pos]
    have h4 : abs (sin T) = sin T := by
      rw [abs_of_pos h2]
    have h5 : abs (cos T) = cos T := by
      rw [abs_of_pos h3]
    rw [h4, h5] at eq1
    nlinarith [Real.sin_pos_of_pos_of_lt_pi (show 0 < T by linarith) (show T < Real.pi by linarith), Real.sin_sq_add_cos_sq T, Real.sin_sq_add_cos_sq T, sq_pos_of_pos h2, sq_pos_of_pos h3, Real.sin_sq_add_cos_sq T, hT_pos]