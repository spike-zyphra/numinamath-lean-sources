import Mathlib

open Real Set
open scoped BigOperators

/- Compute the minimum value of $cos(a-b) + cos(b-c) + cos(c-a)$ as $a,b,c$  ranges over the real numbers. -/
theorem calculus_28115 :
  IsLeast {x : ℝ | ∃ a b c, x = cos (a - b) + cos (b - c) + cos (c - a)} (-3 / 2) := by
  constructor
  · -- We need to prove that -3/2 is achievable
    use 0, 2 * Real.pi / 3, 4 * Real.pi / 3
    have h1 : cos (0 - 2 * Real.pi / 3) = -1 / 2 := by 
      have h2 : cos (0 - 2 * Real.pi / 3) = cos (2 * Real.pi / 3) := by 
        rw [show 0 - 2 * Real.pi / 3 = -(2 * Real.pi / 3) by ring]
        rw [cos_neg]
      rw [h2]
      have h3 : cos (2 * Real.pi / 3) = -1 / 2 := by
        have h4 : cos (2 * Real.pi / 3) = -1 / 2 := by 
          have h5 : cos (2 * Real.pi / 3) = -cos (Real.pi / 3) := by 
            rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring]
            rw [cos_pi_sub]
          rw [h5]
          rw [cos_pi_div_three]
          norm_num
        exact h4
      exact h3
    have h2 : cos (2 * Real.pi / 3 - 4 * Real.pi / 3) = -1 / 2 := by 
      have h3 : 2 * Real.pi / 3 - 4 * Real.pi / 3 = -(2 * Real.pi / 3) := by 
        linarith [Real.pi_pos]
      rw [h3]
      have h4 : cos (-(2 * Real.pi / 3)) = -1 / 2 := by 
        rw [cos_neg]
        have h5 : cos (2 * Real.pi / 3) = -1 / 2 := by 
          have h6 : cos (2 * Real.pi / 3) = -1 / 2 := by 
            have h7 : cos (2 * Real.pi / 3) = -cos (Real.pi / 3) := by 
              rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring]
              rw [cos_pi_sub]
            rw [h7]
            rw [cos_pi_div_three]
            norm_num
          exact h6
        rw [h5]
      rw [h4]
    have h3 : cos (4 * Real.pi / 3 - 0) = -1 / 2 := by 
      have h4 : cos (4 * Real.pi / 3 - 0) = cos (4 * Real.pi / 3) := by 
        simp
      rw [h4]
      have h5 : cos (4 * Real.pi / 3) = -1 / 2 := by 
        have h6 : 4 * Real.pi / 3 = Real.pi + Real.pi / 3 := by 
          linarith [Real.pi_pos]
        rw [h6]
        have h7 : cos (Real.pi + Real.pi / 3) = -cos (Real.pi / 3) := by 
          rw [cos_add]
          simp [cos_pi, sin_pi]
        rw [h7]
        rw [cos_pi_div_three]
        norm_num
      rw [h5]
    linarith [h1, h2, h3]
  · -- Now we need to prove that -3/2 is the least element in the set
    intro x
    rintro ⟨a, b, c, hx⟩
    have h1 : cos (a - b) + cos (b - c) + cos (c - a) ≥ -3 / 2 := by 
      have h2 : (cos a + cos b + cos c) ^ 2 + (sin a + sin b + sin c) ^ 2 ≥ 0 := by 
        apply add_nonneg
        · apply sq_nonneg
        · apply sq_nonneg
      have h3 : (cos a + cos b + cos c) ^ 2 + (sin a + sin b + sin c) ^ 2 =
          3 + 2 * (cos (a - b) + cos (b - c) + cos (c - a)) := by 
        have h4 : (cos a + cos b + cos c) ^ 2 + (sin a + sin b + sin c) ^ 2 =
            (cos a ^ 2 + sin a ^ 2) + (cos b ^ 2 + sin b ^ 2) + (cos c ^ 2 + sin c ^ 2) +
              2 * (cos a * cos b + cos b * cos c + cos c * cos a + sin a * sin b + sin b * sin c + sin c * sin a) := by 
          ring_nf
        have h5 : (cos a ^ 2 + sin a ^ 2) = 1 := by 
          exact Real.cos_sq_add_sin_sq a
        have h6 : (cos b ^ 2 + sin b ^ 2) = 1 := by 
          exact Real.cos_sq_add_sin_sq b
        have h7 : (cos c ^ 2 + sin c ^ 2) = 1 := by 
          exact Real.cos_sq_add_sin_sq c
        rw [h4, h5, h6, h7]
        have h8 : 2 * (cos a * cos b + cos b * cos c + cos c * cos a + sin a * sin b + sin b * sin c + sin c * sin a) = 
          2 * (cos (a - b) + cos (b - c) + cos (c - a)) := by 
          have h9 : cos (a - b) = cos a * cos b + sin a * sin b := by 
            exact Real.cos_sub a b
          have h10 : cos (b - c) = cos b * cos c + sin b * sin c := by 
            exact Real.cos_sub b c
          have h11 : cos (c - a) = cos c * cos a + sin c * sin a := by 
            exact Real.cos_sub c a
          linarith [h9, h10, h11]
        linarith [h8]
      linarith [sq_nonneg (cos a + cos b + cos c), sq_nonneg (sin a + sin b + sin c)]
    -- show (cos (a - b) + cos (b - c) + cos (c - a)) equals two sum of squares - 3 / 2, then x ≥ - 3 / 2. 
    rw [hx] 
    exact h1