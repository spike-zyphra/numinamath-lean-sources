import Mathlib

open Real
/--
Problem statement (Main theorem of this file):
2. The sum of all values of $a$ that make the equation
$$
\frac{x+1}{x-1}+\frac{x-1}{x+1}+\frac{2 x+a+2}{x^{2}-1}=0
$$

have only one real root is
$\qquad$

-/


theorem algebra_299469 (a : ℝ) :
    (∃! x : ℝ, x ≠ 1 ∧ x ≠ -1 ∧ (x + 1) / (x - 1) + (x - 1) / (x + 1) + (2 * x + a + 2) / (x ^ 2 - 1) = 0) ↔
    a = -3.5 ∨ a = -8 ∨ a = -4 := by

  have h_simp: (∃! x : ℝ, x ≠ 1 ∧ x ≠ -1 ∧ (x + 1) / (x - 1) + (x - 1) / (x + 1) + (2 * x + a + 2) / (x ^ 2 - 1) = 0) ↔
  (∃! x : ℝ, x ≠ 1 ∧ x ≠ -1 ∧ 2 * x ^ 2 + 2 * x + a + 4 = 0) := by
    apply existsUnique_congr
    intro x
    simp
    intro h_ne_one h_ne_neg_one
    have : x - 1 ≠ 0 := by
      by_contra h
      have : x = 1 := by linarith
      contradiction

    have : x + 1 ≠ 0 := by
      by_contra h
      have : x = -1 := by linarith
      contradiction

    have : x ^ 2 - 1 ≠ 0 := by
      by_contra h
      have : (x-1)*(x+1) = 0 := by linarith
      field_simp at this

    have : (x + 1) / (x - 1) + (x - 1) / (x + 1) + (2 * x + a + 2) / (x ^ 2 - 1) = (2 * x^2+2*x+a+4)/(x ^ 2 - 1) := by
      field_simp
      ring_nf

    rw [this, div_eq_zero_iff]
    simp
    intro h
    contradiction

  rw [h_simp]
  constructor
  . intro h1
    rcases h1 with ⟨x, ⟨⟨hx_ne_one, hx_ne_neg_one,hx_eq⟩, hy⟩⟩
    by_cases ha1: a > -3.5
    . have : 2 * x ^ 2 + 2 * x + a + 4 > 0 := by
        have : 2 * x ^ 2 + 2 * x + a + 4 = 2* (x + 1/2)^2 + a + 3.5 := by ring
        have : 2* (x + 1/2)^2 ≥ 0 := by positivity
        have : a+3.5 >0 := by linarith
        linarith
      linarith
    . by_cases ha2: a = -3.5
      . left; assumption
      . have ha3: a < -3.5 := by
          simp at ha1
          exact lt_of_le_of_ne ha1 ha2
        by_cases ha4: a = -8
        . right; left; assumption
        . by_cases ha5: a = -4
          . right; right; assumption
          . let x1 := (-1 + sqrt (-7 - 2 * a)) / 2
            let x2 := (-1 - sqrt (-7 - 2 * a)) / 2

            have h_x1_ne_one: x1 ≠ 1 := by
              unfold x1
              field_simp
              by_contra h
              have : √(-7 - 2 * a) ^ 2 = -7 - 2 * a := by rw [sq_sqrt (by linarith)]
              have : -7 - 2 * a = 9 := by
                rw [(by linarith: √(-7 - 2 * a) = 3)] at this
                linarith
              have : a = -8 := by linarith
              contradiction

            have h_x1_ne_neg_one: x1 ≠ -1 := by
              unfold x1
              field_simp
              by_contra h
              have : √(-7 - 2 * a) = -1 := by linarith
              have : √(-7 - 2 * a) > 0 := by positivity
              linarith

            have h_x2_ne_one: x2 ≠ 1 := by
              unfold x2
              field_simp
              by_contra h
              have : √(-7 - 2 * a) = -3 := by linarith
              have : √(-7 - 2 * a) > 0 := by positivity
              linarith

            have h_x2_ne_neg_one: x2 ≠ -1 := by
              unfold x2
              field_simp
              by_contra h
              have : √(-7 - 2 * a) ^ 2 = -7 - 2 * a := by rw [sq_sqrt (by linarith)]
              have : -7 - 2 * a = 1 := by
                rw [(by linarith: √(-7 - 2 * a) = 1)] at this
                linarith
              have : a = -4 := by linarith
              contradiction

            have hx1: 2 * x1 ^ 2 + 2 * x1 + a + 4 = 0 := by
              unfold x1
              ring_nf
              rw [sq_sqrt (by linarith)]
              field_simp

            have hx2: 2 * x2 ^ 2 + 2 * x2 + a + 4 = 0 := by
              unfold x2
              ring_nf
              rw [sq_sqrt (by linarith)]
              field_simp

            have hy1:= hy x1
            simp at hy1
            have hy1' := hy1 h_x1_ne_one h_x1_ne_neg_one hx1
            have hy2:= hy x2
            simp at hy2
            have hy2' := hy2 h_x2_ne_one h_x2_ne_neg_one hx2

            have : x2 ≠ x1 := by
              unfold x1 x2
              field_simp

              by_contra h
              have : √(-7 - 2 * a) = 0 := by linarith
              rw [sqrt_eq_zero'] at this
              linarith

            rw [hy1', hy2'] at this
            contradiction

  . intro ha
    rcases ha with (rfl | rfl | rfl)
    . use (- 1/2)
      simp
      ring_nf
      constructor
      . simp
        constructor
        . linarith
        . linarith
      . intro y hy_ne_one hy_ne_neg_one hy_eq
        rw [(by ring: 1 / 2 + y * 2 + y ^ 2 * 2 = 1/2 * (1 + 2 * y)^2)] at hy_eq
        rw [mul_eq_zero] at hy_eq
        cases hy_eq
        . linarith
        . nlinarith

    . use -2
      simp
      ring_nf
      constructor
      . simp; linarith
      . intro y hy_ne_one hy_ne_neg_one hy_eq
        rw [(by ring: -4 + y * 2 + y ^ 2 * 2 = 2 * (-1 + y) * (2 + y))] at hy_eq
        rw [mul_eq_zero] at hy_eq
        cases hy_eq
        . have : y= 1 := by linarith
          contradiction
        . nlinarith

    . use 0
      simp
      intro y hy_ne_one hy_ne_neg_one hy_eq
      rw [(by ring: 2 * y ^ 2 + 2 * y = (2 * y) * (y + 1))] at hy_eq
      rw [mul_eq_zero] at hy_eq
      cases hy_eq
      . linarith
      . have : y = -1 := by linarith
        contradiction
