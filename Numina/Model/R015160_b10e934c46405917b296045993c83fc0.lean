import Mathlib

open Real
open scoped BigOperators

theorem inequalities_208509 {a b c : ℝ} (h : a > 0) (h' : b > 0) (h'' : c > 0)
  (h''' : a^2 + b^2 = c^2) :
  (1/2) * a * b ≤ ((a + b + c)/2)^2 / 5.5 := by
  have h1 : c^2 = a^2 + b^2 := by 
    linarith

  have h2 : (1 / 2) * a * b ≤ ((a + b + c)/2)^2 / 5.5 := by
    have h3 : ((a + b + c)/2)^2 / 5.5 - (1 / 2) * a * b ≥ 0 := by
      have h5 : c^2 = a^2 + b^2 := by
        linarith

      have h6 : ((a + b + c) / 2 )^2 / 5.5 - (1 / 2) * a * b = ( (a + b + c)^2 / 4 / 5.5 - (1 / 2) * a * b ) := by 
        field_simp
        <;> ring

      rw [h6]

      have h7 : (a + b + c)^2 / 4 / 5.5 - (1 / 2) * a * b = ( (a + b + c)^2 / (22) ) - (1 / 2) * a * b := by
        ring_nf

      rw [h7]

      have h8 : (a + b + c)^2 / (22) - (1 / 2) * a * b ≥ 0 := by

        have h81 : c^2 = a^2 + b^2 := by 
          linarith
        have h9 : a * b > 0 := by
          nlinarith
        have h10 : (a + b + c) ^ 2 ≥ 11 * (a * b) := by
          nlinarith [sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
            sq_nonneg (a - b), sq_nonneg (a * c - b * c), sq_nonneg (a * b - b * c), sq_nonneg (a * b - a * c), 
            mul_pos h h', mul_pos h h'', mul_pos h' h'', 
            h81, 
            sq_nonneg (c^2 - (a^2 + b^2))
            ]
        have h11 : (a + b + c)^2 / (22) - (1 / 2) * a * b ≥ 0 := by
          have h12 : (a + b + c)^2 / (22) - (1 / 2) * a * b = ( (a + b + c) ^ 2 - 11 * (a * b) ) / 22 := by
            field_simp
            <;> ring
          rw [h12]
          apply div_nonneg 
          linarith
          all_goals norm_num
        linarith

      linarith

    linarith

  linarith