import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_9080 {f : ℝ → ℝ}
  (hf : f = λ x => Matrix.det !![sin x + cos x, cos (π - x); 2 * sin x, cos x - sin x]) :
  IsLeast {T | 0 < T ∧ Function.Periodic f T} (Real.pi) := by

  have h1 : ∀ x, f x = (sin x + cos x) * (cos x - sin x) - (cos (π - x)) * (2 * sin x) := by
    intro x
    rw [hf]
    simp [Matrix.det_fin_two]

  have h2 : ∀ x, f x = (sin x + cos x) * (cos x - sin x) - (-cos x) * (2 * sin x) := by
    intro x
    rw [h1 x]
    have h3 : cos (π - x) = -cos x := by
      rw [cos_pi_sub]
    simp [h3]

  have h3 : ∀ x, f x = sin (2 * x) + cos (2 * x) := by
    intro x
    rw [h2 x]
    have h4 : (sin x + cos x) * (cos x - sin x) - (-cos x) * (2 * sin x) = cos (2 * x) + sin (2 * x) := by
      have h5 : (sin x + cos x) * (cos x - sin x) = cos x ^ 2 - sin x ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (sin x - cos x), sq_nonneg (sin x + cos x)]
      have h6 : (-cos x) * (2 * sin x) = -2 * sin x * cos x := by ring
      have h7 : cos (2 * x) = cos x ^ 2 - sin x ^ 2 := by rw [cos_two_mul, sin_sq]; ring
      have h8 : sin (2 * x) = 2 * sin x * cos x := by rw [sin_two_mul]
      calc
        (sin x + cos x) * (cos x - sin x) - (-cos x) * (2 * sin x)
          = (sin x + cos x) * (cos x - sin x) + cos x * (2 * sin x) := by ring
        _ = (cos x ^ 2 - sin x ^ 2) + (2 * sin x * cos x) := by
          rw [h5]
          all_goals
            ring_nf
        _ = cos (2 * x) + sin (2 * x) := by
          rw [h7, h8]
          all_goals
            nlinarith
    linarith

  have h4 : Function.Periodic f Real.pi := by
    unfold Function.Periodic
    intro x
    rw [h3 (x + Real.pi), h3 x]
    have h9 : sin (2 * (x + Real.pi)) = sin (2 * x) := by
      have h10 : 2 * (x + Real.pi) = 2 * x + 2 * Real.pi := by ring
      rw [h10]
      rw [sin_add_two_pi]
    have h10 : cos (2 * (x + Real.pi)) = cos (2 * x) := by
      have h11 : 2 * (x + Real.pi) = 2 * x + 2 * Real.pi := by ring
      rw [h11]
      rw [cos_add_two_pi]
    simp [h9, h10]

  constructor
  · -- Show that π is in the set
    constructor
    . -- Show that 0 < π
      exact pi_pos
    . -- Show that f is periodic with period π
      exact h4
  · -- Show that π is the least element in the set
    intro T ⟨ht_pos, ht_period⟩
    by_contra h
    push_neg at h

    have h5 : Function.Periodic f T := ht_period
    have h9 : ∀ x, f (x + T) = f x := by
      intro x
      exact h5 x

    have eq1 := h9 (Real.pi / 2 - T / 2)
    have eq2 : f (Real.pi / 2 - T / 2 + T) = f (Real.pi / 2 - T / 2) := by linarith [eq1]

    have eq3 : f (Real.pi / 2 - T / 2 + T) = - sin T - cos T := by
      have h12 : f (Real.pi / 2 - T / 2 + T) = sin (2 * (Real.pi / 2 - T / 2 + T)) + cos (2 * (Real.pi / 2 - T / 2 + T)) := by
        apply h3
      rw [h12]
      have h13 : 2 * (Real.pi / 2 - T / 2 + T) = Real.pi + T := by
        ring_nf
      rw [h13]
      have h14 : sin (Real.pi + T) = - sin T := by
        rw [sin_add, sin_pi, cos_pi]
        ring
      have h15 : cos (Real.pi + T) = - cos T := by
        rw [cos_add, sin_pi, cos_pi]
        ring
      simp [h14, h15]
      all_goals
        linarith

    have eq4 : f (Real.pi / 2 - T / 2) = sin T - cos T := by
      have h16 : f (Real.pi / 2 - T / 2) = sin (2 * (Real.pi / 2 - T / 2)) + cos (2 * (Real.pi / 2 - T / 2)) := by
        apply h3
      rw [h16]
      have h17 : 2 * (Real.pi / 2 - T / 2) = Real.pi - T := by
        ring_nf
      rw [h17]
      have h18 : sin (Real.pi - T) = sin T := by
        rw [sin_sub, sin_pi, cos_pi]
        ring
      have h19 : cos (Real.pi - T) = - cos T := by
        rw [cos_sub, sin_pi, cos_pi]
        ring
      simp [h18, h19]
      all_goals
        linarith

    rw [eq3, eq4] at eq2
    have h10 : sin T = 0 := by
      nlinarith [eq2]

    have h11 : sin T > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      all_goals
      linarith [ht_pos, h, Real.pi_gt_three]

    linarith [h10, h11]