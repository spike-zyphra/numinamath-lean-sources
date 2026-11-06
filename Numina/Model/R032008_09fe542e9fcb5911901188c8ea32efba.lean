import Mathlib

open Real Set
open scoped Real

theorem calculus_13255 :
  IsLeast {x : ℝ | 0 < x ∧ 8 * sin x * cos x ^ 5 - 8 * sin x ^ 5 * cos x = 1} (7.5 * π / 180) := by 
  constructor
  · -- Show that 7.5 * π / 180 is in the set.
    constructor
    · -- Show that it's positive.
      have h1 : 0 < 7.5 * π / 180 := by 
        nlinarith [Real.pi_pos]
      linarith
    · -- Show that it satisfies the equation.
      have h2 : 8 * sin (7.5 * π / 180) * cos (7.5 * π / 180) ^ 5 - 8 * sin (7.5 * π / 180) ^ 5 * cos (7.5 * π / 180) = 1 := by
        have h3 : 8 * sin (7.5 * π / 180) * cos (7.5 * π / 180) ^ 5 - 8 * sin (7.5 * π / 180) ^ 5 * cos (7.5 * π / 180) = 2 * sin (4 * (7.5 * π / 180)) := by
          have h31 : 8 * sin (7.5 * π / 180) * cos (7.5 * π / 180) ^ 5 - 8 * sin (7.5 * π / 180) ^ 5 * cos (7.5 * π / 180) = 8 * sin (7.5 * π / 180) * cos (7.5 * π / 180) * (cos (7.5 * π / 180) ^ 4 - sin (7.5 * π / 180) ^ 4) := by 
            ring_nf
          rw [h31]
          have h32 : cos (7.5 * π / 180) ^ 4 - sin (7.5 * π / 180) ^ 4 = (cos (7.5 * π / 180) ^ 2 - sin (7.5 * π / 180) ^ 2) * (cos (7.5 * π / 180) ^ 2 + sin (7.5 * π / 180) ^ 2) := by 
            ring_nf
          have h33 : cos (7.5 * π / 180) ^ 2 + sin (7.5 * π / 180) ^ 2 = 1 := by 
            have h4 : sin (7.5 * π / 180) ^ 2 + cos (7.5 * π / 180) ^ 2 = 1 := by 
              exact Real.sin_sq_add_cos_sq (7.5 * π / 180)
            linarith
          rw [h32, h33]
          have h34 : sin (4 * (7.5 * π / 180)) = 2 * sin (2 * (7.5 * π / 180)) * cos (2 * (7.5 * π / 180)) := by 
            rw [show 4 * (7.5 * π / 180) = 2 * (2 * (7.5 * π / 180)) by ring]
            rw [sin_two_mul]
          have h35 : sin (2 * (7.5 * π / 180)) = 2 * sin (7.5 * π / 180) * cos (7.5 * π / 180) := by 
            rw [sin_two_mul]
          have h36 : cos (2 * (7.5 * π / 180)) = cos (7.5 * π / 180) ^ 2 - sin (7.5 * π / 180) ^ 2 := by 
            rw [cos_two_mul]
            rw [sin_sq, cos_sq]
            <;> ring_nf 
          rw [h34, h35, h36]
          all_goals ring_nf
        rw [h3] 
        have h4 : 4 * (7.5 * π / 180) = Real.pi / 6 := by
          ring_nf
        rw [h4]
        have h5 : sin (Real.pi / 6) = 1 / 2 := by 
          rw [sin_pi_div_six]
        rw [h5]
        all_goals linarith 
      linarith [h2]
  · -- Show that it's minimal.
    intro x ⟨hx_pos, hx_eq⟩
    by_contra h
    push_neg at h 
    have h1 : 8 * sin x * cos x ^ 5 - 8 * sin x ^ 5 * cos x = 2 * sin (4 * x) := by
      have h31 : 8 * sin x * cos x ^ 5 - 8 * sin x ^ 5 * cos x = 8 * sin x * cos x * (cos x ^ 4 - sin x ^ 4) := by 
        ring_nf
      have h32 : cos x ^ 4 - sin x ^ 4 = (cos x ^ 2 - sin x ^ 2) * (cos x ^ 2 + sin x ^ 2) := by 
        ring_nf
      have h33 : cos x ^ 2 + sin x ^ 2 = 1 := by 
        have h34 : sin x ^ 2 + cos x ^ 2 = 1 := by 
          exact Real.sin_sq_add_cos_sq x 
        linarith
      calc 
        8 * sin x * cos x ^ 5 - 8 * sin x ^ 5 * cos x
          = 8 * sin x * cos x * (cos x ^ 4 - sin x ^ 4) := by 
            ring_nf 
        _ = 8 * sin x * cos x * ((cos x ^ 2 - sin x ^ 2) * (cos x ^ 2 + sin x ^ 2)) := by 
          rw [h32]
        _ = 8 * sin x * cos x * (cos x ^ 2 - sin x ^ 2) := by
          rw [h33]
          <;> ring_nf 
        _ = 4 * (2 * sin x * cos x) * (cos x ^ 2 - sin x ^ 2) := by
          ring_nf 
        _ = 2 * sin (4 * x) := by 
          have h36 : sin (4 * x) = 2 * sin (2 * x) * cos (2 * x) := by 
            rw [show 4 * x = 2 * (2 * x) by ring]
            rw [sin_two_mul]
          have h37 : sin (2 * x) = 2 * sin x * cos x := by 
            rw [sin_two_mul]
          have h38 : cos (2 * x) = cos x ^ 2 - sin x ^ 2 := by 
            rw [cos_two_mul]
            rw [sin_sq]
            <;> ring_nf
          rw [h36, h37, h38]
          <;> ring_nf 
    have eq1 : 2 * sin (4 * x) = 1 := by 
      linarith [h1, hx_eq]
    have h3 : 4 * x < Real.pi / 6 := by
      nlinarith [Real.pi_pos, h, Real.pi_pos]
    have h4x_pos : 0 < 4 * x := by 
      nlinarith [Real.pi_pos, hx_pos, Real.pi_pos]
    have h8 : sin (4 * x) < sin (Real.pi / 6) := by 
      apply sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals linarith [Real.pi_pos, h3, show Real.pi / 6 ≤ Real.pi / 2 by linarith [Real.pi_pos], Real.pi_pos]
    have h9 : sin (Real.pi / 6) = 1 / 2 := by 
      rw [sin_pi_div_six]
    nlinarith [eq1, h8, h9]