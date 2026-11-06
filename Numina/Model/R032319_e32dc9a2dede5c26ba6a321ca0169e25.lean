import Mathlib
open Real Set

theorem algebra_9078 {f : ℝ → ℝ} (hf : f = λ x => √2 * sin (x + π / 4)) :
    StrictMonoOn f (Icc 0 (π / 4)) ∧ StrictAntiOn f (Icc (π / 4) π) := by
  constructor
  · -- Prove that f is strictly increasing on [0, π/4]
    intro x hx y hy hxy
    rw [hf]
    simp at hx hy ⊢
    have h1 : x + π / 4 < y + π / 4 := by linarith
    have h2 : sin (x + π / 4) < sin (y + π / 4) := by
      apply sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals
        linarith [Real.pi_pos, hx.1, hy.2]
    have h3 : √2 * sin (x + π / 4) < √2 * sin (y + π / 4) := by
      have h4 : 0 < √2 := by positivity
      nlinarith
    linarith
  · -- Prove that f is strictly decreasing on [π/4, π]
    intro x hx y hy hxy
    rw [hf]
    simp at hx hy ⊢
    have h1 : x + π / 4 < y + π / 4 := by linarith
    have h4 : sin (x + π / 4) > sin (y + π / 4) := by
      have h43 : sin (x + π / 4) = sin (π - (x + π / 4)) := by
        rw [show π - (x + π / 4) = π - (x + π / 4) by rfl]
        rw [sin_pi_sub]
      have h44 : sin (y + π / 4) = sin (π - (y + π / 4)) := by
        rw [show π - (y + π / 4) = π - (y + π / 4) by rfl]
        rw [sin_pi_sub]
      rw [h43, h44]
      have h45 : π - (y + π / 4) < π - (x + π / 4) := by linarith
      have h46 : sin (π - (x + π / 4)) > sin (π - (y + π / 4)) := by
        apply sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals
          linarith [Real.pi_pos, hx.1, hx.2, hy.1, hy.2, hxy]
      linarith
    have h3 : √2 * sin (x + π / 4) > √2 * sin (y + π / 4) := by
      have h4 : 0 < √2 := by positivity
      nlinarith
    linarith