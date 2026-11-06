import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_323908 {f : ℝ → ℝ} (hf : ∀ x ∈ Ioo (-π/2) (π/2), f (tan x) = sin (2*x)) :
    IsGreatest {y | ∃ x, y = f (2 * sin x)} 1 := by
  constructor
  · -- Show that 1 is in the set
    use Real.pi / 6
    have h1 : f 1 = 1 := by
      specialize hf (Real.pi / 4) (by
        constructor
        · -- Show that -π/2 < π/4
          linarith [Real.pi_pos]
        · -- Show that π/4 < π/2
          linarith [Real.pi_pos]
      )
      have h2 : tan (Real.pi / 4) = 1 := by
        rw [tan_pi_div_four]
      have h3 : sin (2 * (Real.pi / 4)) = 1 := by
        have h4 : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
        rw [h4]
        rw [sin_pi_div_two]
      rw [show tan (Real.pi / 4) = 1 by linarith [h2], show sin (2 * (Real.pi / 4)) = 1 by linarith [h3]] at hf
      linarith
    have h2 : 2 * sin (Real.pi / 6) = 1 := by
      have h3 : sin (Real.pi / 6) = 1 / 2 := sin_pi_div_six
      linarith
    rw [h2]
    linarith [h1]
  · -- Show that 1 is the greatest element in the set
    intro y
    rintro ⟨x, hx⟩
    rw [hx]
    have h2 : f (2 * sin x) = sin (2 * (Real.arctan (2 * sin x)) ) := by 
      have h3 : Real.arctan (2 * sin x) ∈ Ioo (-Real.pi / 2) (Real.pi / 2) := by
        constructor
        · -- Show that -π/2 < arctan (2 * sin x)
          have h3 : -Real.pi / 2 < Real.arctan (2 * sin x) := by
            linarith [Real.neg_pi_div_two_lt_arctan (2 * sin x), Real.arctan_lt_pi_div_two (2 * sin x)]
          linarith
        · -- Show that arctan (2 * sin x) < π/2
          have h4 : Real.arctan (2 * sin x) < Real.pi / 2 := Real.arctan_lt_pi_div_two (2 * sin x)
          linarith
      have h4 : f (tan (Real.arctan (2 * sin x))) = sin (2 * Real.arctan (2 * sin x)) := by
        apply hf
        exact h3
      have h5 : tan (Real.arctan (2 * sin x)) = 2 * sin x := by
        rw [tan_arctan]
      rw [h5] at h4
      linarith
    have h3 : sin (2 * (Real.arctan (2 * sin x)) ) ≤ 1 := by
      have h4 : sin (2 * (Real.arctan (2 * sin x)) ) ≤ 1 := by 
        apply sin_le_one
      linarith
    linarith [h2, h3]