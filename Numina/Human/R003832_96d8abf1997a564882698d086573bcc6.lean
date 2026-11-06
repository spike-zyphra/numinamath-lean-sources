import Mathlib

open Real

set_option maxHeartbeats 300000

theorem algebra_215098 {a : ℝ} :
  (∃! x : ℝ × ℝ, x.1 - x.2 = a * (1 + x.1 * x.2) ∧ x.1 + x.2 + x.1 * x.2 + 2 = 0) ↔
  a = -1 ∨ a = 1 ∨ a = 2 / sqrt 5 ∨ a = - (2 / sqrt 5) := by

  have h_sqrt5a: √5 ^ 3 = 5 * √5 := by
    rw [pow_three]
    simp
    linarith

  have h_sqrt5b: √5-2 ≠ 0 := by
    by_contra
    have : √5 = 2 := by linarith
    rw [sqrt_eq_iff_eq_sq (by positivity) (by positivity)] at this
    norm_num at this

  constructor
  . intro hx
    rcases hx with ⟨⟨x, y⟩, ⟨h1, h2⟩, h3⟩
    simp at h1 h2 h3

    by_contra ha0
    simp at ha0

    have ha1 : a ^ 2 ≠ 1 := by
      by_contra
      have : (a-1)*(a+1) = 0 := by linarith
      simp at this
      rcases this with h1 | h2
      . have : a = 1 := by linarith
        tauto
      . have : a = -1 := by linarith
        tauto

    have : a + 1 ≠ 0 := by
      by_contra
      have : a = -1 := by linarith
      tauto

    have : a - 1 ≠ 0 := by
      by_contra
      have : a = 1 := by linarith
      tauto

    have : 2*a + 2 ≠ 0 := by
      by_contra
      have : a = -1 := by linarith
      tauto

    have : 2*a - 2 ≠ 0 := by
      by_contra
      have : a = 1 := by linarith
      tauto

    have ha2: a ^ 2 ≥ 4/5 := by
      by_contra h_contra
      simp at h_contra
      have : x*y=-x-y-2 := by linarith
      rw [this] at h1

      have : (a+1)*x+(a-1)*y = -a := by linarith
      have : y = (-a-(a+1)*x)/(a-1) := by field_simp; linarith
      rw [this] at h2
      field_simp at h2
      ring_nf at h2

      have : x ^ 2 = ((-2 + (-(x * 2) - x * a) + a) / (a + 1)) := by field_simp; linarith

      have : ((1 + a) * x + 1 + a/2)^2 = (-4 + 5 * a^2)/4 := by
        ring_nf
        rw [this]
        field_simp
        ring_nf

      nlinarith

    have ha3: a ^ 2 > 4/5 := by
      have : a ^ 2 ≠ 4/5 := by
        by_contra
        have : (a-2/√5)*(a+2/√5) = 0 := by
          ring_nf
          field_simp
          linarith

        simp at this
        rcases this with h1 | h2
        . have : a = 2/√5 := by linarith
          tauto
        . have : a = -(2/√5) := by nlinarith
          tauto

      exact lt_of_le_of_ne ha2 (Ne.symm this)


    let x1 := (-(2 + a + √(-4 + 5 * a ^ 2))/(2*a+2))
    let y1 := ((2 - a + √(-4 + 5 * a ^ 2))/(2*a-2))
    let x2 := (-(2 + a - √(-4 + 5 * a ^ 2))/(2*a+2))
    let y2 := ((2 - a - √(-4 + 5 * a ^ 2))/(2*a-2))

    have h1eq1: x1 - y1 = a * (1 + x1 * y1) := by
      unfold x1 y1
      field_simp
      ring_nf
      rw [sq_sqrt (by linarith)]
      ring_nf

    have h1eq2: x1 + y1 + x1 * y1 + 2 = 0 := by
      unfold x1 y1
      field_simp
      ring_nf
      rw [sq_sqrt (by linarith)]
      ring_nf

    have h2eq1: x2 - y2 = a * (1 + x2 * y2) := by
      unfold x2 y2
      field_simp
      ring_nf
      rw [sq_sqrt (by linarith)]
      ring_nf

    have h2eq2: x2 + y2 + x2 * y2 + 2 = 0 := by
      unfold x2 y2
      field_simp
      ring_nf
      rw [sq_sqrt (by linarith)]
      ring_nf

    have heq1 := h3 x1 y1 h1eq1 h1eq2
    have heq2 := h3 x2 y2 h2eq1 h2eq2

    have : x1 = x2 := by rw [heq1.1, heq2.1]

    unfold x1 x2 at this
    field_simp at this

    have : √(-4 + 5 * a ^ 2) = 0 := by linarith
    rw [sqrt_eq_zero (by linarith)] at this
    nlinarith

  . intro ha
    rcases ha with rfl | rfl | rfl | rfl
    . use (-3, -1/2)
      simp
      constructor
      . norm_num
      . intro a b ha hb
        have h1: b = -1/2 := by linarith
        rw [h1] at hb
        have h2: a = -3 := by linarith
        exact ⟨h2, h1⟩

    . use (-1/2, -3)
      simp
      constructor
      . norm_num
      . intro a b ha hb
        have h1: a = -1/2 := by linarith
        rw [h1] at hb
        have h2: b = -3 := by linarith
        exact ⟨h1, h2⟩

    . use (-3+sqrt 5, -3-sqrt 5)
      simp
      constructor
      . norm_num
        ring_nf
        rw [sq_sqrt (by positivity)]
        field_simp
        ring_nf
        rw [sq_sqrt (by positivity)]
        norm_num
      . intro a b ha hb
        have : a*b = -2-a-b := by linarith
        rw [this] at ha
        have h1: a = 4 - 2* sqrt 5 + (9 - 4 *sqrt 5)* b := by
          -- have : √5 ≠ 0 := by positivity
          field_simp at ha
          have : a * (√5+2) = b * √5 -2 - 2*b := by linarith
          rw [← mul_left_inj' h_sqrt5b] at this
          ring_nf at this
          rw [sq_sqrt (by positivity)] at this
          ring_nf at this
          linarith
        rw [h1] at hb
        ring_nf at hb

        have : (9 - 4 * sqrt 5) * (b + 3 + sqrt 5)^2 = 0 := by
          suffices (9 - 4 * √5) * (b + 3 + √5) ^ 2 - 0 = 0 by linarith
          nth_rw 1 [← hb]
          ring_nf
          rw [sq_sqrt (by positivity)]
          rw [h_sqrt5a]
          norm_num
          ring_nf

        simp at this
        have : b + 3 + √5 = 0 := by
          rcases this
          . have : √5 = 9/4 := by linarith
            rw [sqrt_eq_iff_eq_sq (by positivity) (by positivity)] at this
            norm_num at this
          . assumption
        have h2 : b = -3-sqrt 5 := by linarith
        have h3 : a = -3+sqrt 5 := by
          rw [h2] at h1
          rw [h1]
          ring_nf
          rw [sq_sqrt (by positivity)]
          linarith

        exact ⟨h3, h2⟩

    . use (-3-sqrt 5, -3+sqrt 5)
      simp
      constructor
      . ring_nf
        field_simp
        ring_nf
        rw [sq_sqrt (by positivity)]
        norm_num

      . intro a b ha hb
        have : a*b = -2-a-b := by linarith
        rw [this] at ha
        have h1: a = 4 + 2*sqrt 5 + (9 + 4*sqrt 5)*b := by
          field_simp at ha
          have : a * (√5-2) = b * √5 + 2 + 2*b := by linarith
          rw [← mul_left_inj' h_sqrt5b] at this
          ring_nf at this
          rw [sq_sqrt (by positivity)] at this
          ring_nf at this
          linarith

        rw [h1] at hb
        ring_nf at hb

        have : (9 + 4 * sqrt 5) * (b + 3 - sqrt 5)^2 = 0 := by
          suffices (9 + 4 * √5) * (b + 3 - √5) ^ 2 - 0 = 0 by linarith
          nth_rw 1 [← hb]
          ring_nf
          rw [sq_sqrt (by positivity)]
          rw [h_sqrt5a]
          norm_num
          ring_nf

        simp at this
        have : b + 3 - √5 = 0 := by
          rcases this
          . have : √5 ≥ 0 := by positivity
            linarith
          . assumption
        have h2 : b = -3+sqrt 5 := by linarith
        have h3 : a = -3-sqrt 5 := by
          rw [h2] at h1
          rw [h1]
          ring_nf
          rw [sq_sqrt (by positivity)]
          linarith

        exact ⟨h3, h2⟩
