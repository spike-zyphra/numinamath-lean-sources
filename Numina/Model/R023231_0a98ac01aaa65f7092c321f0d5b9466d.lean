import Mathlib

open Real Set

theorem algebra_3602 {x : ℝ} (hx : cos (x * π / 180) ^ 2 - sin (x * π / 180) = 1 / 4) (hx1 : 0 < x ∧ x < 90): x = 30 := by
  rcases hx1 with ⟨hx1, hx2⟩
  have h1 : cos (x * π / 180) ^ 2 + sin (x * π / 180) ^ 2 = 1 := by
    exact Real.cos_sq_add_sin_sq (x * π / 180)
  have h2 : cos (x * π / 180) ^ 2 = 1 - sin (x * π / 180) ^ 2 := by
    linarith 
  rw [h2] at hx
  have h3 : (sin (x * π / 180) - 1 / 2) * (sin (x * π / 180) + 3 / 2) = 0 := by 
    nlinarith 
  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- If $\sin(x * \pi / 180) = 1/2$, then $x = 30$.
    have h8 : sin (x * π / 180) = 1 / 2 := by linarith 
    -- If `sin(A) = 1/2` and `A` is in the first quadrant, then `A = π/6`.
    -- Prove angle is in the first quadrant.
    have h9 : 0 < x * π / 180 := by
      nlinarith [Real.pi_pos]
    have h10 : x * π / 180 < Real.pi / 2 := by 
      have h111 : Real.pi / 2 = (90 : ℝ) * (Real.pi / 180) := by
        ring_nf 
      have h112 : x * π / 180 < (90 : ℝ) * (Real.pi / 180) := by
        have h13 : Real.pi / 180 > 0 := by 
          nlinarith [Real.pi_pos]
        have h14 : x < (90 : ℝ) := by linarith
        nlinarith [Real.pi_pos]
      linarith [h111, h112]
    have h14 : x * π / 180 = Real.pi / 6 := by
      have h115 : sin (x * π / 180) = 1 / 2 := h8
      have h116 : x * π / 180 = Real.arcsin (sin (x * π / 180)) := by
        rw [Real.arcsin_sin]
        all_goals
          nlinarith [Real.pi_pos, h10, h9]
      rw [h115] at h116
      have h118 : Real.arcsin (1 / 2) = Real.pi / 6 := by 
        have h119 : Real.sin (Real.pi / 6) = 1 / 2 := by 
          exact Real.sin_pi_div_six 
        rw [← h119] 
        apply Real.arcsin_sin 
        all_goals
          linarith [Real.pi_pos]
      rw [h118] at h116 
      linarith
    have h15 : x = 30 := by
      nlinarith [Real.pi_pos, h14]
    linarith
  · -- $\sin(x * \pi / 180) = -3/2$ is impossible.
    have h6 : sin (x * π / 180) = -3 / 2 := by linarith 
    have h7 : -1 ≤ sin (x * π / 180) ∧ sin (x * π / 180) ≤ 1 := by
      apply sin_mem_Icc 
    nlinarith