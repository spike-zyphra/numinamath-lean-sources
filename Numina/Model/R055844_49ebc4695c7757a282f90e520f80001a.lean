import Mathlib

theorem algebra_161104 {a b : ℝ} (ha : 0 < a ∧ a ≠ 1) (hb : 0 < b ∧ b ≠ 1)
    (h : Real.logb a 2 = Real.logb (a / 2) 4) (h' : Real.logb (a / 2) 4 = Real.logb b 3) :
    a = 1 / 2 ∧ b = 1 / 3 := by
  have ha1 : 0 < a := ha.1
  have ha2 : a ≠ 1 := ha.2
  have hb1 : 0 < b := hb.1
  have hb2 : b ≠ 1 := hb.2
  have h1 : Real.logb a 2 = Real.log 2 / Real.log a := by
    field_simp [Real.logb]
  have h2 : Real.logb (a / 2) 4 = Real.log 4 / Real.log (a / 2) := by
    field_simp [Real.logb]
  have h3 : Real.log (a / 2) = Real.log a - Real.log 2 := by
    rw [Real.log_div (by linarith) (by linarith)]
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    simp [Real.log_pow]
  rw [h1, h2, h3, h4] at h
  have h5 : Real.log 2 ≠ 0 := by
    positivity
  have h6 : Real.log a ≠ 0 := by
    have h7 : a > 0 := ha1
    have h8 : a ≠ 1 := ha2
    have : Real.log a ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one h7 h8
    assumption
  have h8 : Real.log a - Real.log 2 ≠ 0 := by
    by_contra h9
    have h10 : Real.log a = Real.log 2 := by linarith
    have h11 : a = 2 := by
      have h12 : Real.log a = Real.log 2 := h10
      have h13 : a > 0 := ha1
      have h14 : (2 : ℝ) > 0 := by norm_num
      have h15 : Real.log a = Real.log (2 : ℝ) := by linarith
      have h16 : a = (2 : ℝ) := by
        exact Real.log_injOn_pos (Set.mem_Ioi.mpr h13) (Set.mem_Ioi.mpr h14) h15
      linarith
    rw [h11] at h
    norm_num [h11] at h
    all_goals linarith
  have eq1 : Real.log 2 * (Real.log a - Real.log 2) = 2 * Real.log 2 * Real.log a := by
    field_simp [h6, h8] at h
    nlinarith
  have eq2 : Real.log a - Real.log 2 = 2 * Real.log a := by
    apply (mul_left_inj' h5).mp
    linarith
  have eq3 : Real.log a = - Real.log 2 := by
    linarith
  have ha3 : a = 1 / 2 := by
    have h10 : Real.log a = - Real.log 2 := eq3
    have h11 : a = (1 / 2 : ℝ) := by
      have h12 : Real.log a = Real.log (1 / 2 : ℝ) := by
        rw [h10]
        have h13 : Real.log (1 / 2 : ℝ) = Real.log 1 - Real.log 2 := by
          field_simp [Real.log_div]
        rw [h13]
        simp [Real.log_one]
      have h13 : a > 0 := ha1
      have h14 : (1 / 2 : ℝ) > 0 := by norm_num
      have h15 : Real.log a = Real.log (1 / 2 : ℝ) := h12
      exact Real.log_injOn_pos (Set.mem_Ioi.mpr h13) (Set.mem_Ioi.mpr h14) h15
    linarith
  have hb3 : b = 1 / 3 := by
    rw [show a = 1 / 2 by linarith [ha3] ] at h'
    have h6 : Real.logb (1 / 2 / 2) 4 = -1 := by
      rw [Real.logb]
      have h7 : Real.log (1 / 2 / 2 : ℝ) = - Real.log 4 := by
        have h8 : (1 / 2 / 2 : ℝ) = (1 / 4 : ℝ) := by ring
        rw [h8]
        have h9 : Real.log (1 / 4 : ℝ) = - Real.log 4 := by
          simp [Real.log_div, Real.log_one]
        linarith
      rw [h7]
      have h8 : Real.log 4 ≠ 0 := by
        have h9 : (4 : ℝ) > 0 := by norm_num
        have h10 : (4 : ℝ) ≠ 1 := by norm_num
        have h11 : Real.log (4 : ℝ) ≠ 0 := by
          apply Real.log_ne_zero_of_pos_of_ne_one h9 h10
        exact h11
      field_simp [h8]
      <;> nlinarith [Real.log_pos (show (4 : ℝ) > 1 by norm_num)]
    have h7 : Real.logb b 3 = Real.log 3 / Real.log b := by
      field_simp [Real.logb]
    rw [h6, h7] at h'
    have h8 : Real.log 3 ≠ 0 := by
      positivity
    have h9 : Real.log b ≠ 0 := by
      have hb3 : b > 0 := hb1
      have hb4 : b ≠ 1 := hb2
      have : Real.log b ≠ 0 := by
        apply Real.log_ne_zero_of_pos_of_ne_one hb3 hb4
      assumption
    field_simp [h9] at h'
    have h10 : Real.log b = - Real.log 3 := by
      linarith
    have hb3 : b = 1 / 3 := by
      have h12 : Real.log b = Real.log (1 / 3 : ℝ) := by
        rw [h10]
        have h13 : Real.log (1 / 3 : ℝ) = - Real.log 3 := by
          simp [Real.log_div, Real.log_one]
        linarith
      have hb3 : b > 0 := hb1
      have hb4 : (1 / 3 : ℝ) > 0 := by norm_num
      have h14 : Real.log b = Real.log (1 / 3 : ℝ) := h12
      exact Real.log_injOn_pos (Set.mem_Ioi.mpr hb3) (Set.mem_Ioi.mpr hb4) h14
    linarith
  constructor
  · linarith [ha3]
  · linarith [hb3]