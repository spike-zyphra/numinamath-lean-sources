import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_169509 :
  IsLeast {x | ∃ a b c : ℝ, x = cos a * sin b + cos b * sin c + cos c * sin a} (-3/2) ∧
  IsGreatest {x | ∃ a b c : ℝ, x = cos a * sin b + cos b * sin c + cos c * sin a} (3/2) := by
  constructor
  · -- Prove that -3/2 is the least
    constructor
    · -- Show that -3/2 is in the set
      -- We set a = 3 * π / 4, b = 3 * π / 4, c = 3 * π / 4
      use (3 * (Real.pi / 4))
      use (3 * (Real.pi / 4))
      use (3 * (Real.pi / 4))
      have h1 : cos (3 * (Real.pi / 4)) = - Real.sqrt 2 / 2 := by
        have h2 : 3 * (Real.pi / 4) = Real.pi - (Real.pi / 4) := by
          nlinarith [Real.pi_pos]
        rw [h2]
        rw [cos_pi_sub]
        have h3 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
          exact cos_pi_div_four
        linarith
      have h2 : sin (3 * (Real.pi / 4)) = Real.sqrt 2 / 2 := by
        have h3 : 3 * (Real.pi / 4) = Real.pi - (Real.pi / 4) := by 
          nlinarith [Real.pi_pos]
        rw [h3]
        rw [sin_pi_sub]
        have h4 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
          exact sin_pi_div_four
        linarith
      rw [h1, h2]
      ring_nf
      <;> norm_num [Real.sq_sqrt]
      <;> ring
    · -- Show that for any x in the set, x >= -3/2
      intro x hx
      rcases hx with ⟨a, b, c, h_eq⟩
      have h : cos a * sin b + cos b * sin c + cos c * sin a ≥ -3 / 2 := by
        have h1 : sin a ^ 2 + cos a ^ 2 = 1 := by
          exact Real.sin_sq_add_cos_sq a
        have h2 : sin b ^ 2 + cos b ^ 2 = 1 := by 
          exact Real.sin_sq_add_cos_sq b
        have h3 : sin c ^ 2 + cos c ^ 2 = 1 := by
          exact Real.sin_sq_add_cos_sq c
        nlinarith [sq_nonneg (cos a - sin b), sq_nonneg (cos b - sin c), sq_nonneg (cos c - sin a), 
                  sq_nonneg (cos a + sin b), sq_nonneg (cos b + sin c), sq_nonneg (cos c + sin a), 
                  Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq b, Real.sin_sq_add_cos_sq c, 
                  sq_nonneg (cos a + cos b + cos c), sq_nonneg (sin a + sin b + sin c), 
                  Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq b, Real.sin_sq_add_cos_sq c, 
                  mul_self_nonneg (cos a - sin b), mul_self_nonneg (cos b - sin c),
                  mul_self_nonneg (cos c - sin a)
              ]
      linarith
  · -- Prove greatest
    constructor
    · -- Show that 3/2 in the set
      use (Real.pi / 4)
      use (Real.pi / 4)
      use (Real.pi / 4)
      have h1 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by 
        exact cos_pi_div_four
      have h2 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by 
        exact sin_pi_div_four
      rw [h1, h2]
      ring_nf
      <;> norm_num [Real.sq_sqrt]
      <;> ring
    · -- Show x <= 3/2
      intro x hx
      rcases hx with ⟨a, b, c, h_eq⟩
      have h : cos a * sin b + cos b * sin c + cos c * sin a ≤ 3 / 2 := by 
        have h1 : sin a ^ 2 + cos a ^ 2 = 1 := by 
          exact Real.sin_sq_add_cos_sq a
        have h2 : sin b ^ 2 + cos b ^ 2 = 1 := by 
          exact Real.sin_sq_add_cos_sq b
        have h3 : sin c ^ 2 + cos c ^ 2 = 1 := by 
          exact Real.sin_sq_add_cos_sq c
        nlinarith [sq_nonneg (cos a - sin b), sq_nonneg (cos b - sin c), sq_nonneg (cos c - sin a), 
                  sq_nonneg (cos a + sin b), sq_nonneg (cos b + sin c), sq_nonneg (cos c + sin a), 
                  Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq b, Real.sin_sq_add_cos_sq c, 
                  sq_nonneg (cos a + cos b + cos c), sq_nonneg (sin a + sin b + sin c), 
                  Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq b, Real.sin_sq_add_cos_sq c, 
                  mul_self_nonneg (cos a - sin b), mul_self_nonneg (cos b - sin c), 
                  mul_self_nonneg (cos c - sin a)
              ]
      linarith