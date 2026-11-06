import Mathlib

theorem algebra_249155 {x y : ℝ} (hy : y ≠ x) (h : 1 / (1 + x ^ 2) + 1 / (1 + y ^ 2) = 2 / (1 + x * y)) :
    1 / (1 + x ^ 2) + 1 / (1 + y ^ 2) + 2 / (1 + x * y) = 2 := by
  have hx1 : 1 + x * y ≠ 0 := by
    by_contra h1
    have eq1 : 1 + x * y = 0 := by linarith
    rw [eq1] at h
    field_simp [(show 1 + x * y = 0 by linarith), show 1 + x ^ 2 ≠ 0 by nlinarith, show 1 + y ^ 2 ≠ 0 by nlinarith] at h
    all_goals
      nlinarith [sq_pos_of_ne_zero (show x - y ≠ 0 by
        intro h'
        apply hy
        nlinarith
      ), sq_pos_of_ne_zero (show (x + y) ≠ 0 by
        by_contra h'
        have h2 : x + y = 0 := by linarith
        nlinarith [sq_pos_of_ne_zero (show x - y ≠ 0 by
          intro h'
          apply hy
          nlinarith
        ), sq_nonneg (x - y)]
      ), sq_nonneg (x - y), sq_nonneg (x + y)]
  have eq1 : (1 + y ^ 2) * (1 + x * y) + (1 + x ^ 2) * (1 + x * y) = 2 * (1 + x ^ 2) * (1 + y ^ 2) := by
    have hx2 : 1 + x ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg x]
    have hy2 : 1 + y ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg y]
    field_simp [hx2, hy2, hx1] at h ⊢
    nlinarith
  have eq2 : (x - y) ^ 2 * (x * y - 1) = 0 := by
    nlinarith [sq_pos_of_ne_zero (show x - y ≠ 0 by
      intro h'
      apply hy
      nlinarith
    ), sq_nonneg (x * y - 1), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * (y)), sq_nonneg ((x - y) * (x + y)), sq_nonneg (x * y * (x - y))]
  cases' (mul_eq_zero.mp eq2) with h3 h4
  · -- We have (x - y) ^ 2 = 0, but x ≠ y, so contradiction
    have h5 : (x - y) ^ 2 = 0 := by
      linarith [h3]
    have h6 : x - y = 0 := by
      apply pow_eq_zero
      exact h5
    have h7 : x = y := by linarith
    exfalso
    apply hy
    linarith
  · -- Now x * y - 1 = 0, i.e., x * y = 1
    have eq3 : x * y = 1 := by linarith
    have h7 : 1 / (1 + x ^ 2) + 1 / (1 + y ^ 2) = 1 := by
      have eq3' : x * y = 1 := eq3
      have hx2 : 1 + x ^ 2 ≠ 0 := by
        nlinarith [sq_nonneg x]
      have hy2 : 1 + y ^ 2 ≠ 0 := by
        nlinarith [sq_nonneg y]
      field_simp [hx2, hy2, show y ≠ 0 by
        by_contra h8
        have h9 : x * y = 0 := by
          rw [show y = (0 : ℝ) by linarith]
          norm_num
        linarith [eq3']
      , show x ≠ 0 by
        by_contra h8
        have h9 : x * y = 0 := by
          rw [show x = (0 : ℝ) by linarith]
          norm_num
        linarith [eq3']
      ] at *
      <;> nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y - 1)]
    have eq8 : 2 / (1 + x * y) = 1 := by
      have eq3' : x * y = 1 := eq3
      rw [show 1 + x * y = 2 by
        nlinarith [eq3']
      ]
      all_goals
        norm_num
    calc
      1 / (1 + x ^ 2) + 1 / (1 + y ^ 2) + 2 / (1 + x * y) = (1 / (1 + x ^ 2) + 1 / (1 + y ^ 2)) + 2 / (1 + x * y) := by ring
      _ = 1 + 2 / (1 + x * y) := by rw [h7]
      _ = 1 + 1 := by rw [eq8]
      _ = 2 := by norm_num