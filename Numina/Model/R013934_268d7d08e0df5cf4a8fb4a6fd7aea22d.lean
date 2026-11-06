import Mathlib

theorem algebra_326505 {p q r k : ℝ} (hpqr : p > 0 ∧ q > 0 ∧ r > 0)
    (h : (p + q + r)^2 / p^2 = k) (h' : 2 * (p + q + r)^2 / q^2 = k)
    (h'' : 3 * (p + q + r)^2 / r^2 = k) :
    k = 6 + 2 * (Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 6) := by
  rcases hpqr with ⟨hp, hq, hr⟩
  have h1 : (p + q + r) ^ 2 / p ^ 2 = 2 * (p + q + r) ^ 2 / q ^ 2 := by
    linarith [h, h']
  have h2 : (p + q + r) ^ 2 > 0 := by
    positivity
  have eq1 : 1 / p ^ 2 = 2 / q ^ 2 := by
    have h3 : (p + q + r) ^ 2 > 0 := h2
    have eq2 : (p + q + r) ^ 2 / p ^ 2 = 2 * (p + q + r) ^ 2 / q ^ 2 := h1
    have eq3 : (p + q + r) ^ 2 / p ^ 2 = ( (p + q + r) ^ 2 ) * (1 / p ^ 2) := by
      field_simp
    have eq4 : 2 * (p + q + r) ^ 2 / q ^ 2 = ( (p + q + r) ^ 2 ) * (2 / q ^ 2) := by
      field_simp
      <;> ring
    rw [eq3, eq4] at eq2
    have h4 : (p + q + r) ^ 2 > 0 := h2
    have eq5 : ( (p + q + r) ^ 2 ) * (1 / p ^ 2) = ( (p + q + r) ^ 2 ) * (2 / q ^ 2) := eq2
    have h5 : (1 / p ^ 2) = (2 / q ^ 2) := by
      apply (mul_left_inj' (ne_of_gt h2)).mp
      linarith
    linarith
  have eq2 : q ^ 2 = 2 * p ^ 2 := by
    field_simp at eq1
    nlinarith
  have h3 : 2 * (p + q + r) ^ 2 / q ^ 2 = 3 * (p + q + r) ^ 2 / r ^ 2 := by
    linarith [h', h'']
  have eq3 : 2 / q ^ 2 = 3 / r ^ 2 := by
    have h4 : (p + q + r) ^ 2 > 0 := h2
    have eq4 : 2 * (p + q + r) ^ 2 / q ^ 2 = 3 * (p + q + r) ^ 2 / r ^ 2 := h3
    have eq5 : 2 * (p + q + r) ^ 2 / q ^ 2 = ( (p + q + r) ^ 2 ) * (2 / q ^ 2) := by
      field_simp
      <;> ring
    have eq6 : 3 * (p + q + r) ^ 2 / r ^ 2 = ( (p + q + r) ^ 2 ) * (3 / r ^ 2) := by
      field_simp
      <;> ring
    rw [eq5, eq6] at eq4
    have h4 : (p + q + r) ^ 2 > 0 := h2
    have eq7 : ( (p + q + r) ^ 2 ) * (2 / q ^ 2) = ( (p + q + r) ^ 2 ) * (3 / r ^ 2) := eq4
    have h5 : (2 / q ^ 2) = (3 / r ^ 2) := by
      apply (mul_left_inj' (ne_of_gt h2)).mp
      linarith
    linarith
  have eq4 : 2 * r ^ 2 = 3 * q ^ 2 := by
    field_simp at eq3
    nlinarith
  have eq5 : q = Real.sqrt 2 * p := by
    have h4 : q ^ 2 = 2 * p ^ 2 := eq2
    have h5 : q > 0 := hq
    have h6 : p > 0 := hp
    have h7 : q = Real.sqrt (2 * p ^ 2) := by
      have h8 : q ^ 2 = 2 * p ^ 2 := h4
      have h9 : q > 0 := hq
      have h10 : q = Real.sqrt (q ^ 2) := by
        rw [Real.sqrt_sq (show 0 ≤ q by linarith)]
      rw [h10, h8]
    have h8 : Real.sqrt (2 * p ^ 2) = Real.sqrt 2 * p := by
      have h9 : Real.sqrt (2 * p ^ 2) = Real.sqrt (2 * (p ^ 2)) := by ring_nf
      have h10 : Real.sqrt (2 * (p ^ 2)) = Real.sqrt 2 * Real.sqrt (p ^ 2) := by
        rw [Real.sqrt_mul (by nlinarith)]
      have h11 : Real.sqrt (p ^ 2) = p := by
        rw [Real.sqrt_sq]
        nlinarith
      rw [h9, h10, h11]
      all_goals nlinarith
    rw [h7, h8]
  have eq6 : r = Real.sqrt 3 * p := by
    have eq7 : 2 * r ^ 2 = 3 * q ^ 2 := eq4
    rw [show q ^ 2 = 2 * p ^ 2 by linarith [eq2] ] at eq7
    have eq8 : r ^ 2 = 3 * p ^ 2 := by
      nlinarith
    have h5 : r > 0 := hr
    have h6 : p > 0 := hp
    have eq9 : r = Real.sqrt (3 * p ^ 2) := by
      have h7 : r ^ 2 = 3 * p ^ 2 := eq8
      have h8 : r > 0 := hr
      have h9 : r = Real.sqrt (r ^ 2) := by
        rw [Real.sqrt_sq (show 0 ≤ r by linarith)]
      rw [h9, h7]
    have eq10 : Real.sqrt (3 * p ^ 2) = Real.sqrt 3 * p := by
      have h7 : Real.sqrt (3 * p ^ 2) = Real.sqrt (3 * (p ^ 2)) := by ring_nf
      have h8 : Real.sqrt (3 * (p ^ 2)) = Real.sqrt 3 * Real.sqrt (p ^ 2) := by
        rw [Real.sqrt_mul (by nlinarith)]
      have h9 : Real.sqrt (p ^ 2) = p := by
        rw [Real.sqrt_sq]
        nlinarith
      rw [h7, h8, h9]
    rw [eq9, eq10]
  have h4 : (p + q + r) ^ 2 / p ^ 2 = (1 + Real.sqrt 2 + Real.sqrt 3) ^ 2 := by
    have eq7 : q = Real.sqrt 2 * p := eq5
    have eq8 : r = Real.sqrt 3 * p := eq6
    rw [eq7, eq8]
    have h5 : p > 0 := hp
    field_simp
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
      Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)]
  have hk : k = (1 + Real.sqrt 2 + Real.sqrt 3) ^ 2 := by
    linarith [h, h4]
  have h5 : (1 + Real.sqrt 2 + Real.sqrt 3) ^ 2 = 6 + 2 * (Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 6) := by
    have h51 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), 
      Real.sqrt_pos.mpr (show (0 : ℝ) < 6 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), 
      h51, mul_pos (Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)) (Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num))
    ]
  rw [hk, h5]
  all_goals linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 6 by norm_num)]