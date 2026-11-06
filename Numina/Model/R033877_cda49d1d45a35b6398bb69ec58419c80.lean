import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_282736 {f : ℝ → ℝ} (hf : f = λ x => abs (sin x)) :
    StrictMonoOn f (Icc 0 (π/2)) ∧ IsLeast {T | 0 < T ∧ f = λ x => f (x + T)} (Real.pi) := by
  constructor
  · -- Verify that f is strictly increasing on [0, π/2].
    intro x hx y hy hxy
    rw [hf]
    have hx1 : 0 ≤ x := by
        simp at hx ⊢
        linarith
    have hx2 : x ≤ π / 2 := by
      simp at hx ⊢
      linarith
    have hy1 : 0 ≤ y := by
      simp at hy ⊢
      linarith
    have hy2 : y ≤ π / 2 := by
      simp at hy ⊢
      linarith
    have h3 : sin x ≥ 0 := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      linarith [Real.pi_pos]
      linarith [Real.pi_pos]
    have h4 : sin y ≥ 0 := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      linarith [Real.pi_pos]
      linarith [Real.pi_pos]
    have h5 : sin x < sin y := by
      apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals linarith [Real.pi_pos, hxy]
    have h6 : abs (sin x) < abs (sin y) := by
      rw [abs_of_nonneg h3, abs_of_nonneg h4]
      linarith
    simpa using h6
  · -- Verify that π is the smallest positive period of f
    constructor
    · -- Show that π is in the set
      constructor
      · -- Show that π > 0
        exact Real.pi_pos
      · -- Show that f = fun x => f (x + π)
        funext x
        rw [hf]
        have hsin : sin (x + π) = - sin x := by
          rw [sin_add, sin_pi, cos_pi]
          ring
        simp only [hsin, abs_neg]
    · -- Show that π is minimal
      intro T ⟨hTpos, hT⟩
      by_contra h
      push_neg at h
      have h1 := congr_fun hT 0
      have eq1 : f 0 = f T := by
        simpa using h1
      have eq2 : f 0 = abs (sin (0 : ℝ)) := by
        rw [hf]
      have eq3 : f T = abs (sin T) := by
        rw [hf]
      have eq4 : abs (sin (0 : ℝ)) = 0 := by
        norm_num [abs_zero]
      have eq7 : abs (sin T) = 0 := by
        rw [eq2] at eq1
        rw [eq4] at eq1
        rw [eq3] at eq1
        linarith
      have eq8 : sin T = 0 := by
        simpa [abs_eq_zero] using eq7
      have h3 : sin T > 0 := by
        apply Real.sin_pos_of_pos_of_lt_pi
        all_goals linarith [hTpos, h, Real.pi_gt_three]
      linarith [h3, eq8]