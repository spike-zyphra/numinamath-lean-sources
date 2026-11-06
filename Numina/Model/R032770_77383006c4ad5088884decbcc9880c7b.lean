import Mathlib

open Real Set
open scoped Real
theorem algebra_3374 (x : ℝ) (hx : x ∈ Icc 0 (Real.pi)) :
    cos x + cos (2 * x) + cos (3 * x) = 0 ↔
    x = Real.pi / 4 ∨ x = 2 * Real.pi / 3 ∨ x = 3 * Real.pi / 4 := by
  constructor
  · -- Assume $\cos(x) + \cos(2x) + \cos(3x) = 0$ and $x \in [0, \pi]$
    intro h
    rcases hx with ⟨hx1, hx2⟩
    have h1 : cos x + cos (2 * x) + cos (3 * x) = 0 := h
    have h2 : cos (2 * x) = 2 * cos x ^ 2 - 1 := by rw [cos_two_mul]
    have h3 : cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x := by
      rw [cos_three_mul]
    
    rw [h2, h3] at h1
    
    have h4 : 4 * cos x ^ 3 + 2 * cos x ^ 2 - 2 * cos x - 1 = 0 := by
      nlinarith [h1]
    
    have h5 : (cos x + 1 / 2) * (4 * cos x ^ 2 - 2) = 0 := by 
      ring_nf at h4 ⊢
      linarith
    
    cases' (mul_eq_zero.mp h5) with h6 h7
    
    · -- Case where $\cos x + 1/2 = 0 \Rightarrow \cos x = -1/2$
      have h8 : cos x = -1 / 2 := by linarith
      have h9 : x = 2 * Real.pi / 3 := by
        have h10 : x = Real.arccos (-1 / 2) := by
          rw [←h8]
          apply Eq.symm
          exact Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
        have h11 : Real.arccos (-1 / 2) = 2 * Real.pi / 3 := by
          have h12 : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
            have h13 : Real.cos (2 * Real.pi / 3) = Real.cos (Real.pi - Real.pi / 3) := by ring_nf
            rw [h13]
            rw [Real.cos_pi_sub]
            norm_num
          have h14 : 0 ≤ 2 * Real.pi / 3 := by linarith [Real.pi_pos]
          have h15 : 2 * Real.pi / 3 ≤ Real.pi := by
            linarith [Real.pi_pos]
          rw [←h12]
          apply Real.arccos_cos h14 h15
        rw [h11] at h10
        exact h10
      right
      left
      exact h9
    · -- Case where $4 \cos^2 x - 2 = 0 \Rightarrow \cos^2 x = 1/2$
      have h13 : 4 * cos x ^ 2 - 2 = 0 := h7
      have h14 : cos x ^ 2 = 1 / 2 := by linarith
      have h15 : cos x = Real.sqrt (1 / 2) ∨ cos x = -Real.sqrt (1 / 2) := by
        have h16 : cos x ^ 2 - (1 / 2) = 0 := by linarith
        have h17 : (cos x - Real.sqrt (1 / 2)) * (cos x + Real.sqrt (1 / 2)) = 0 := by 
          have h18 : (cos x - Real.sqrt (1 / 2)) * (cos x + Real.sqrt (1 / 2)) = cos x ^ 2 - (Real.sqrt (1 / 2)) ^ 2 := by ring
          rw [h18]
          have h19 : (Real.sqrt (1 / 2)) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
          rw [h19]
          linarith
        cases (mul_eq_zero.mp h17) with
        | inl h20 => 
          left
          linarith
        | inr h21 => 
          right
          linarith
      cases' h15 with h16 h17
      · -- Case where $\cos x = \sqrt{1/2} = \frac{\sqrt{2}}{2}$
        have h18 : x = Real.pi / 4 := by
          have h19 : x = Real.arccos (Real.sqrt (1 / 2)) := by
            rw [←h16]
            apply Eq.symm
            exact Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
          have h20 : Real.arccos (Real.sqrt (1 / 2)) = Real.pi / 4 := by
            have h21 : Real.sqrt (1 / 2) = Real.sqrt 2 / 2 := by
              rw [show (1 / 2 : ℝ) = (2 : ℝ) / (2 ^ 2) by ring]
              field_simp
            rw [h21]
            have h22 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
            have h23 : 0 ≤ Real.pi / 4 := by linarith [Real.pi_pos]
            have h24 : Real.pi / 4 ≤ Real.pi := by linarith [Real.pi_pos]
            rw [←h22]
            apply Real.arccos_cos h23 h24
          rw [h20] at h19
          exact h19
        left
        exact h18
      · -- Case where $\cos x = -\sqrt{1/2} = -\frac{\sqrt{2}}{2}$
        have h18 : x = 3 * Real.pi / 4 := by
          have h19 : x = Real.arccos (-Real.sqrt (1 / 2)) := by
            rw [←h17]
            apply Eq.symm
            exact Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
          have h20 : Real.arccos (-Real.sqrt (1 / 2)) = 3 * Real.pi / 4 := by
            have h21 : Real.cos (3 * Real.pi / 4) = -Real.sqrt 2 / 2 := by
              have h22 : 3 * Real.pi / 4 = Real.pi - Real.pi / 4 := by ring
              rw [h22]
              rw [Real.cos_pi_sub]
              have h23 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
              linarith
            have h24 : 0 ≤ 3 * Real.pi / 4 := by linarith [Real.pi_pos]
            have h25 : 3 * Real.pi / 4 ≤ Real.pi := by
              linarith [Real.pi_pos]
            have h26 : -Real.sqrt (1 / 2) = -Real.sqrt 2 / 2 := by
              have h27 : Real.sqrt (1 / 2) = Real.sqrt 2 / 2 := by
                rw [show (1 / 2 : ℝ) = (2 : ℝ) / (2 ^ 2) by ring]
                field_simp
              linarith
            rw [h26]
            have h28 : Real.arccos (-Real.sqrt 2 / 2) = 3 * Real.pi / 4 := by
              have h29 : Real.cos (3 * Real.pi / 4) = -Real.sqrt 2 / 2 := h21
              have h30 : 0 ≤ 3 * Real.pi / 4 := by linarith [Real.pi_pos]
              have h31 : 3 * Real.pi / 4 ≤ Real.pi := by
                linarith [Real.pi_pos]
              rw [←h29]
              apply Real.arccos_cos h30 h31
            exact h28
          rw [h20] at h19
          exact h19
        right
        right
        exact h18
  · -- Verify that $\cos(x) + \cos(2x) + \cos(3x) = 0$ when $x \in \{\pi/4, 2\pi/3, 3\pi/4\}$
    rintro (h | h | h)
    · -- $x = \pi / 4$
      rw [h]
      have h1 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
      have h2 : cos (2 * (Real.pi / 4)) = 0 := by
        have h3 : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
        rw [h3]
        exact Real.cos_pi_div_two
      have h3 : cos (3 * (Real.pi / 4)) = -Real.sqrt 2 / 2 := by
        have h4 : 3 * (Real.pi / 4) = Real.pi - Real.pi / 4 := by ring
        rw [h4]
        rw [Real.cos_pi_sub]
        have h5 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
        linarith
      nlinarith [h1, h2, h3, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ 2)]
    · -- $x = 2\pi / 3$
      rw [h]
      have h1 : cos (2 * Real.pi / 3) = -1 / 2 := by
        have h2 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
        rw [h2]
        rw [Real.cos_pi_sub]
        have h3 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
        linarith
      have h2 : cos (2 * (2 * Real.pi / 3)) = -1 / 2 := by
        have h3 : 2 * (2 * Real.pi / 3) = Real.pi + Real.pi / 3 := by ring
        rw [h3]
        have h4 : Real.cos (Real.pi + Real.pi / 3) = -1 / 2 := by
          rw [Real.cos_add]
          rw [Real.cos_pi, Real.sin_pi]
          have h5 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
          have h6 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
          rw [h5, h6]
          ring
        exact h4
      have h3 : cos (3 * (2 * Real.pi / 3)) = 1 := by
        have h4 : 3 * (2 * Real.pi / 3) = 2 * Real.pi := by ring
        rw [h4]
        exact Real.cos_two_pi
      nlinarith [h1, h2, h3]
    · -- $x = 3\pi / 4$
      rw [h]
      have h1 : cos (3 * Real.pi / 4) = -Real.sqrt 2 / 2 := by
        have h2 : 3 * Real.pi / 4 = Real.pi - Real.pi / 4 := by ring
        rw [h2]
        rw [Real.cos_pi_sub]
        have h3 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
        linarith
      have h2 : cos (2 * (3 * Real.pi / 4)) = 0 := by
        have h3 : 2 * (3 * Real.pi / 4) = Real.pi + Real.pi / 2 := by ring
        rw [h3]
        have h4 : Real.cos (Real.pi + Real.pi / 2) = 0 := by
          rw [Real.cos_add]
          rw [Real.cos_pi, Real.sin_pi]
          have h5 : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
          have h6 : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
          rw [h5, h6]
          ring
        exact h4
      have h3 : cos (3 * (3 * Real.pi / 4)) = Real.sqrt 2 / 2 := by
        have h4 : 3 * (3 * Real.pi / 4) = 2 * Real.pi + Real.pi / 4 := by ring
        rw [h4]
        have h5 : cos (2 * Real.pi + Real.pi / 4) = cos (Real.pi / 4) := by
          rw [cos_add, cos_two_pi, sin_two_pi]
          ring
        rw [h5]
        exact Real.cos_pi_div_four
      nlinarith [h1, h2, h3, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ 2)]