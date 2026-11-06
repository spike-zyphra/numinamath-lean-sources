import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_116137 {f : ℝ → ℝ} (hf : f = λ x => cos x ^ 4 + sin x ^ 2) :
    IsLeast {T | 0 < T ∧ f = λ x => f (x + T)} (Real.pi / 2) := by
  constructor
  · -- Show that π/2 is in the set
    constructor
    · -- Show that π/2 > 0
      linarith [Real.pi_pos]
    · -- Show that f = λ x => f (x + Real.pi / 2)
      funext x
      have h1 : f x = f (x + Real.pi / 2) := by
        rw [hf]
        have h3 : cos (x + Real.pi / 2) = - sin x := by
          rw [cos_add, cos_pi_div_two, sin_pi_div_two]
          ring
        have h4 : sin (x + Real.pi / 2) = cos x := by
          rw [sin_add, cos_pi_div_two, sin_pi_div_two]
          ring
        simp [h3, h4]
        <;> nlinarith [Real.cos_sq_add_sin_sq x, sq_nonneg (cos x ^ 2 - sin x ^ 2), sq_nonneg (cos x * sin x)]
      simpa using h1
  · -- Show that π/2 is the least element in the set
    intro T ⟨hTpos, hf_eq⟩
    by_contra h
    push_neg at h
    -- Assume T < π/2, derive a contradiction
    have eq1 := congr_fun hf_eq 0
    have eq1' : f 0 = f T := by simpa using eq1
    rw [hf] at eq1'
    simp at eq1'
    -- Now eq1' is cos T ^ 4 + sin T ^ 2 = 1
    have h6 : cos T ^ 2 = 0 ∨ cos T ^ 2 = 1 := by
      have h7 : cos T ^ 4 + (1 - cos T ^ 2) = 1 := by
        have h8 : sin T ^ 2 = 1 - cos T ^ 2 := by
          linarith [Real.sin_sq_add_cos_sq T]
        nlinarith
      have h8 : cos T  ^ 4 - cos T ^ 2 = 0 := by linarith
      have h9 : cos T ^ 2 * (cos T ^ 2 - 1) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h9) with h10 h11
      · -- cos T ^ 2 = 0
        left
        linarith
      · -- cos T ^ 2 - 1 = 0
        right
        linarith
    rcases h6 with h6 | h6
    · -- cos^2 T = 0
      have h7 : cos T = 0 := by
        nlinarith
      have h8 : cos T > 0 := by
        apply Real.cos_pos_of_mem_Ioo
        constructor
        · -- Show that -Real.pi / 2 < T
          linarith [hTpos, Real.pi_pos, h6, show T < Real.pi / 2 by linarith]
        · -- Show that T < Real.pi / 2
          linarith [hTpos, Real.pi_pos, h6, show T < Real.pi / 2 by linarith]
      nlinarith
    · -- cos^2 T = 1
      have h8 : sin T ^ 2 = 0 := by
        have h9 : sin T ^ 2 + cos T ^ 2 = 1 := by
          linarith [Real.sin_sq_add_cos_sq T]
        nlinarith
      have h9 : sin T = 0 := by
        nlinarith
      have h10 : sin T > 0 := by
        apply Real.sin_pos_of_pos_of_lt_pi
        linarith [hTpos, Real.pi_pos]
        linarith [hTpos, Real.pi_pos, show T < Real.pi by linarith [Real.pi_gt_three, hTpos]]
      nlinarith