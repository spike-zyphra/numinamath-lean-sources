import Mathlib

open Real Set
open scoped Real

theorem calculus_598948 : IsGreatest {x | ∃ t : ℝ, t ∈ Ioo 0 Real.pi ∧ x = sin t / (2 + cos t)} (sqrt 3 / 3) := by
  constructor
  · -- Show that sqrt 3 / 3 is in the set
    use (2 * Real.pi / 3)
    constructor
    · -- Show that 2 * Real.pi / 3 is in the interval (0, Real.pi)
      constructor
      · -- Show it's greater than 0
        nlinarith [Real.pi_pos]
      · -- Show it's less than Real.pi
        nlinarith [Real.pi_pos]
    · -- Show that sqrt 3 / 3 equals sin (2 * Real.pi / 3) / (2 + cos (2 * Real.pi / 3))
      have h1 : sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
        have h2 : sin (2 * Real.pi / 3) = sin (Real.pi - (Real.pi / 3)) := by
          ring_nf
        rw [h2]
        rw [sin_pi_sub]
        have h3 : sin (Real.pi / 3) = Real.sqrt 3 / 2 := by
          exact sin_pi_div_three
        linarith
      have h4 : cos (2 * Real.pi / 3) = -1 / 2 := by
        have h5 : cos (2 * Real.pi / 3) = cos (Real.pi - (Real.pi / 3)) := by
          ring_nf
        rw [h5]
        rw [cos_pi_sub]
        have h6 : cos (Real.pi / 3) = 1 / 2 := by
          exact cos_pi_div_three
        linarith
      rw [h1, h4]
      field_simp
      <;> nlinarith
  · -- Show that sqrt 3 / 3 is the greatest element in the set
    intro x hx
    rcases hx with ⟨t, ht, rfl⟩
    rcases ht with ⟨ht1, ht2⟩
    have h14 : 0 < sin t := by
      apply sin_pos_of_pos_of_lt_pi
      linarith
      linarith
    have ht61 : 0 < 2 + cos t := by
      nlinarith [Real.sin_sq_add_cos_sq t, h14, Real.cos_sq_add_sin_sq t]
    have h221 : sin t / (2 + cos t) ≤ sqrt 3 / 3 := by
      have ht3 : 0 < 2 + cos t := ht61
      have h7 : sin t / (2 + cos t) ≤ Real.sqrt 3 / 3 := by
        have h9 : 0 < 2 + cos t := ht3
        have ht22 : Real.sqrt 3 * sin t - cos t ≤ 2 := by
          have h12 : sin (t - Real.pi / 6) = sin t * cos (Real.pi / 6) - cos t * sin (Real.pi / 6) := by 
            rw [show t - Real.pi / 6 = t - Real.pi / 6 by rfl]
            rw [sin_sub]
          have h13 : sin (Real.pi / 6) = 1 / 2 := sin_pi_div_six
          have h14 : cos (Real.pi / 6) = Real.sqrt 3 / 2 := cos_pi_div_six
          have h15 : sin (t - Real.pi / 6) = (sin t * Real.sqrt 3 / 2 - cos t * 1 / 2) := by
            rw [h12, h13, h14]
            <;> ring
          have h16 : Real.sqrt 3 * sin t - cos t = 2 * sin (t - Real.pi / 6) := by
            nlinarith [h15]
          have h17 : sin (t - Real.pi / 6) ≤ 1 := by 
            apply sin_le_one
          have h18 : Real.sqrt 3 * sin t - cos t ≤ 2 := by
            nlinarith [h16, h17]
          nlinarith
        have sqrt3_pos : Real.sqrt 3 > 0 := by positivity
        apply (div_le_iff₀ ht3).mpr
        nlinarith [Real.sqrt_nonneg 3, Real.sin_sq_add_cos_sq t, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      exact h7
    linarith [h221]