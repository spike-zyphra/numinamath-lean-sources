import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_12010 {f : ℝ → ℝ}
  (hf : f = λ x => (sqrt 3 * sin x + cos x) * (sqrt 3 * cos x - sin x)) :
  IsLeast {x | 0 < x ∧ f = λ y => f (y + x)} (Real.pi) := by
  constructor
  · -- Show that π is in the set
    constructor
    · -- Show that π > 0
      exact Real.pi_pos
    · -- Show that f = fun y => f (y + π)
      funext y 
      rw [hf]
      have h1 : sin (y + Real.pi) = -sin y := by 
        rw [sin_add_pi]
      have h2 : cos (y + Real.pi) = -cos y := by 
        rw [cos_add_pi]
      simp [h1, h2]
      <;> ring_nf <;> simp [mul_add, add_mul]
      <;> ring
  · -- Show that π is least such positive period
    intro T ⟨hT_pos, h_eq⟩
    by_contra h
    push_neg at h
    have eq4 := congr_fun h_eq (Real.pi / 2 - T / 2)
    have eq5 : f (Real.pi / 2 - T / 2) = f (Real.pi / 2 - T / 2 + T) := by
      simpa using eq4
    have eq6 : f (Real.pi / 2 - T / 2) = (sqrt 3 * sin (Real.pi / 2 - T / 2) + cos (Real.pi / 2 - T / 2)) * (sqrt 3 * cos (Real.pi / 2 - T / 2) - sin (Real.pi / 2 - T / 2)) := by
      rw [hf]
    have eq7 : f (Real.pi / 2 - T / 2 + T) = (sqrt 3 * sin (Real.pi / 2 - T / 2 + T) + cos (Real.pi / 2 - T / 2 + T)) * (sqrt 3 * cos (Real.pi / 2 - T / 2 + T) - sin (Real.pi / 2 - T / 2 + T)) := by
      rw [hf]
    have h7 : sin (Real.pi / 2 - T / 2) = cos (T / 2) := by
      have h1 : sin (Real.pi / 2 - T / 2) = cos (T / 2) := by
        rw [show Real.pi / 2 - T / 2 = Real.pi / 2 - (T / 2) by ring]
        rw [sin_pi_div_two_sub]
        all_goals linarith
      exact h1
    have h8 : cos (Real.pi / 2 - T / 2) = sin (T / 2) := by
      have h1 : cos (Real.pi / 2 - T / 2) = sin (T / 2) := by
        rw [show Real.pi / 2 - T / 2 = Real.pi / 2 - (T / 2) by ring]
        rw [cos_pi_div_two_sub]
        all_goals linarith
      exact h1
    have h9 : sin (Real.pi / 2 - T / 2 + T) = cos (T / 2) := by
      have h2 : Real.pi / 2 - T / 2 + T = Real.pi / 2 + T / 2 := by
        ring_nf
      rw [h2]
      have h3 : sin (Real.pi / 2 + T / 2) = cos (T / 2) := by
        rw [sin_add]
        simp [sin_pi_div_two, cos_pi_div_two]
        all_goals ring_nf <;> simp [cos_sq]
        all_goals ring_nf <;> simp [cos_sq]
        all_goals ring
      exact h3
    have h10 : cos (Real.pi / 2 - T / 2 + T) = -sin (T / 2) := by
      have h2 : Real.pi / 2 - T / 2 + T = Real.pi / 2 + T / 2 := by
        ring_nf
      rw [h2]
      have h3 : cos (Real.pi / 2 + T / 2) = -sin (T / 2) := by
        rw [cos_add]
        simp [sin_pi_div_two, cos_pi_div_two]
        all_goals ring_nf <;> simp [sin_sq, cos_sq] 
        all_goals ring_nf <;> simp [sin_sq, cos_sq] 
      exact h3
    rw [eq6, eq7] at eq5
    simp only [h7, h8, h9, h10] at eq5
    have eq8 : sin T = 0 := by
      have ht2 : (sqrt 3 * cos (T / 2) + sin (T / 2)) * (sqrt 3 * sin (T / 2) - cos (T / 2)) = (sqrt 3 * cos (T / 2) - sin (T / 2)) * (-sqrt 3 * sin (T / 2) - cos (T / 2)) := by
        linarith [eq5]
      have ht3 : sin T = 2 * sin (T / 2) * cos (T / 2) := by
        rw [←sin_two_mul]
        ring_nf
      have ht4 : cos T = 2 * cos (T / 2) ^ 2 - 1 := by
        rw [←cos_two_mul]
        ring_nf
      nlinarith [sq_nonneg (sin (T / 2)), sq_nonneg (cos (T / 2) - 1 / 2), sq_nonneg (cos (T / 2) - 0), sq_nonneg (sin (T / 2) - 0), sq_nonneg (sin T), sq_nonneg (cos T - 1), sq_nonneg (cos T + 1), Real.sin_sq_add_cos_sq T, Real.sin_sq_add_cos_sq (T / 2), Real.sqrt_pos.mpr (show 0 < 3 by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0)]
    -- But since T ∈ (0, π), sin T > 0, which contradicts sin T = 0.
    have eq9 : sin T > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith
      linarith [Real.pi_gt_three, show T < Real.pi by linarith]
    linarith [eq8, eq9]