import Mathlib

open Real Set
open scoped BigOperators


theorem calculus_28115 :
  IsLeast {x : ℝ | ∃ a b c, x = cos (a - b) + cos (b - c) + cos (c - a)} (-3 / 2) := by
  constructor
  ·
    use (0 : ℝ), (2 * Real.pi / 3 : ℝ), (4 * Real.pi / 3 : ℝ)
    have h1 : cos (0 - 2 * Real.pi / 3) = -1 / 2 := by
      have h1 : cos (0 - 2 * Real.pi / 3) = cos (2 * Real.pi / 3) := by
        have h2 : 0 - 2 * Real.pi / 3 = -(2 * Real.pi / 3) := by ring
        rw [h2]
        rw [cos_neg]
      rw [h1]
      have h2 : cos (2 * Real.pi / 3) = -1 / 2 := by
        have h3 : cos (2 * Real.pi / 3) = -cos (Real.pi / 3) := by
          rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring]
          rw [cos_pi_sub]
        rw [h3]
        rw [cos_pi_div_three]
        all_goals norm_num
      linarith
    have h2 : cos (2 * Real.pi / 3 - 4 * Real.pi / 3) = -1 / 2 := by
      have h3 : cos (2 * Real.pi / 3 - 4 * Real.pi / 3) = cos (- (2 * Real.pi / 3)) := by
        ring_nf
      rw [h3]
      have h4 : cos (- (2 * Real.pi / 3)) = cos (2 * Real.pi / 3) := by
        rw [cos_neg]
      rw [h4]
      have h5 : cos (2 * Real.pi / 3) = -1 / 2 := by
        have h6 : cos (2 * Real.pi / 3) = -cos (Real.pi / 3) := by
          rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring]
          rw [cos_pi_sub]
        rw [h6]
        rw [cos_pi_div_three]
        all_goals norm_num
      linarith
    have h3 : cos (4 * Real.pi / 3 - (0 : ℝ)) = -1 / 2 := by
      have h4 : cos (4 * Real.pi / 3 - (0 : ℝ)) = cos (4 * Real.pi / 3) := by
        ring_nf
      rw [h4]
      have h5 : cos (4 * Real.pi / 3) = -1 / 2 := by
        have h6 : cos (4 * Real.pi / 3) = cos (Real.pi + Real.pi / 3) := by
          ring_nf
        rw [h6]
        have h7 : cos (Real.pi + Real.pi / 3) = -cos (Real.pi / 3) := by
          rw [cos_add]
          rw [cos_pi, sin_pi]
          all_goals ring
        rw [h7]
        rw [cos_pi_div_three]
        all_goals norm_num
      linarith
    -- Show that -3/2 = cos (0 - 2*π/3) + cos (2*π/3 - 4*π/3) + cos (4*π/3 - 0)
    have eq1 : cos (0 - 2 * Real.pi / 3) + cos (2 * Real.pi / 3 - 4 * Real.pi / 3) + cos (4 * Real.pi / 3 - (0 : ℝ)) = -3 / 2 := by
      linarith [h1, h2, h3]
    linarith [eq1]
  ·
    intro x
    rintro ⟨a, b, c, hx⟩
    have h1 : cos (a - b) + cos (b - c) + cos (c - a) ≥ -3 / 2 := by
      have h1 : cos (a - b) = cos a * cos b + sin a * sin b := by rw [cos_sub]
      have h2 : cos (b - c) = cos b * cos c + sin b * sin c := by rw [cos_sub]
      have h3 : cos (c - a) = cos c * cos a + sin c * sin a := by rw [cos_sub]
      rw [h1, h2, h3]
      nlinarith [sq_nonneg (cos a + cos b + cos c), sq_nonneg (sin a + sin b + sin c), 
          sq_nonneg (cos a - cos b), sq_nonneg (cos b - cos c), sq_nonneg (cos c - cos a),
          sq_nonneg (sin a - sin b), sq_nonneg (sin b - sin c), sq_nonneg (sin c - sin a),
          Real.cos_sq_add_sin_sq a, Real.cos_sq_add_sin_sq b, Real.cos_sq_add_sin_sq c,
          sq_nonneg (cos a + cos b + cos c), sq_nonneg (sin a + sin b + sin c)]
    linarith [hx, h1]