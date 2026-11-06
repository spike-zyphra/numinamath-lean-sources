import Mathlib

open Complex

theorem algebra_124628 :
  ∃ (z1 z2 z3 : ℂ), z1 ≠ z2 ∧ z2 ≠ z3 ∧ z3 ≠ z1
  ∧ z1^3 + 1 = 0 ∧ z2^3 + 1 = 0 ∧ z3^3 + 1 = 0
  ∧ dist z1 z2 = dist z1 z3 ∧ dist z1 z2 = dist z2 z3 := by

  have h_sqrt3: √3 ^ 2 = 3 := by rw [Real.sq_sqrt (by norm_num)]

  use -1, 1/2+(√3/2)*I, 1/2-(√3/2)*I

  have h_dist1: dist (-1) (1/2+(√3/2)*I) = √3 := by
    rw [dist_eq]
    rw [sub_add_eq_sub_sub]
    rw [(by norm_num : (-1: ℂ) - 1/2 = -3/2)]

    have := normSq_add_mul_I (-3/2) (-√3/2)
    rw [normSq_eq_norm_sq] at this
    norm_num at this
    ring_nf at this
    rw [h_sqrt3] at this
    norm_num at this
    nth_rw 2 [← h_sqrt3] at this
    rw [sq_eq_sq₀ (by positivity)] at this
    suffices -(3 / 2) + -(↑√3 * I * (1 / 2)) = -3 / 2 - ↑√3 / 2 * I by
      rw [← this]
      assumption

    ring_nf
    field_simp

  have h_dist2: dist (-1) (1/2-(√3/2)*I) = √3 := by
    rw [dist_eq]
    ring_nf

    have := normSq_add_mul_I (-3/2) (√3/2)
    rw [normSq_eq_norm_sq] at this
    norm_num at this
    ring_nf at this
    rw [h_sqrt3] at this
    norm_num at this
    nth_rw 2 [← h_sqrt3] at this
    rw [sq_eq_sq₀ (by positivity) (by positivity)] at this
    suffices -(3 / 2) + ↑√3 * I * (1 / 2) = -3 / 2 + ↑√3 * I * (1 / 2) by
      rw [← this]
      assumption

    field_simp

  have h_dist3: dist (1/2+(√3/2)*I) (1/2-(√3/2)*I) = √3 := by
    rw [dist_eq]
    ring_nf
    simp

  constructor
  . by_contra h_contra
    have := congr_arg re h_contra
    simp at this
    norm_num at this

  . constructor
    . by_contra h_contra
      have := congr_arg im h_contra
      simp at this
      have : √3 = 0 := by linarith
      rw [Real.sqrt_eq_zero'] at this
      linarith

    . constructor
      . by_contra h_contra
        have := congr_arg im h_contra
        simp at this

      . constructor
        . norm_num
        . have h1: √3 ^ 3 = 3 * √3 := by
            rw [(by norm_num : 3 = 2+1)]
            rw [pow_add]
            rw [h_sqrt3]
            linarith
          have h2: I ^ 3 = -I := by
            rw [pow_three]
            simp
          constructor
          . ring_nf
            norm_cast
            rw [h1]
            rw [h2]
            field_simp
            ring_nf
          . constructor
            . ring_nf
              norm_cast
              rw [h1]
              rw [h2]
              simp
              push_cast
              field_simp
              ring_nf

            . constructor
              . rw [h_dist1, h_dist2]
              . rw [h_dist3, h_dist1]
