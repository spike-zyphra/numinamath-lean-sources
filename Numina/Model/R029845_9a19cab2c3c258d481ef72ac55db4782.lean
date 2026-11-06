import Mathlib

theorem algebra_106327 (a b c : ℝ) (ha : 0 < a ∧ a ≠ 1) (hb : 0 < b ∧ b ≠ 1) (hc : 0 < c ∧ c ≠ 1)
    (h : Real.logb a 2018 + Real.logb c 2018 = 2 * Real.logb b 2018) :
    Real.logb a 2019 + Real.logb c 2019 = 2 * Real.logb b 2019 ∧ a^2 = (a * c)^(Real.logb c b) := by

  have h1 : Real.logb a 2018 = Real.log 2018 / Real.log a := by
    field_simp [Real.logb]
  have h2 : Real.logb c 2018 = Real.log 2018 / Real.log c := by
    field_simp [Real.logb]
  have h3 : Real.logb b 2018 = Real.log 2018 / Real.log b := by
    field_simp [Real.logb]
  rw [h1, h2, h3] at h

  have h4 : Real.log 2018 > 0 := by
    apply Real.log_pos
    all_goals norm_num
  have h5 : Real.log 2018 > 0 := h4

  have ha2 : Real.log a ≠ 0 := by
    have ha_pos : a > 0 := ha.1
    have ha_ne₁ : a ≠ 1 := ha.2
    exact Real.log_ne_zero_of_pos_of_ne_one ha_pos ha_ne₁
  have hb2 : Real.log b ≠ 0 := by
    have hb_pos : b > 0 := hb.1
    have hb_ne₁ : b ≠ 1 := hb.2
    exact Real.log_ne_zero_of_pos_of_ne_one hb_pos hb_ne₁
  have hc2 : Real.log c ≠ 0 := by
    have hc_pos : c > 0 := hc.1
    have hc_ne₁ : c ≠ 1 := hc.2
    exact Real.log_ne_zero_of_pos_of_ne_one hc_pos hc_ne₁

  have h6 : 1 / Real.log a + 1 / Real.log c = 2 / Real.log b := by
    have h5 : Real.log 2018 * (1 / Real.log a + 1 / Real.log c) = 2 * Real.log 2018 / Real.log b := by
      field_simp [ha2, hc2, hb2] at h ⊢
      nlinarith
    have h7 : Real.log 2018 > 0 := h4
    have h8 : Real.log 2018 ≠ 0 := by linarith
    have eq1 : Real.log 2018 * (1 / Real.log a + 1 / Real.log c) = 2 * Real.log 2018 / Real.log b := h5
    have eq4 : 1 / Real.log a + 1 / Real.log c = 2 / Real.log b := by
      apply (mul_left_inj' (show Real.log 2018 ≠ 0 by linarith)).mp
      field_simp [hb2] at eq1 ⊢
      nlinarith
    exact eq4

  have h9 : Real.logb a 2019 + Real.logb c 2019 = 2 * Real.logb b 2019 := by
    have h10 : Real.logb a 2019 = Real.log 2019 / Real.log a := by
      field_simp [Real.logb]
    have h11 : Real.logb c 2019 = Real.log 2019 / Real.log c := by
      field_simp [Real.logb]
    have h12 : Real.logb b 2019 = Real.log 2019 / Real.log b := by
      field_simp [Real.logb]
    rw [h10, h11, h12]

    have h20 : Real.log 2019 > 0 := by
      apply Real.log_pos
      all_goals norm_num
    have h21 : Real.log 2019 ≠ 0 := by linarith

    field_simp [ha2, hc2, hb2, h21] at *
    <;> nlinarith [h6]
  have h100 : a ^ 2 = (a * c) ^ (Real.logb c b) := by
    have pos1 : a > 0 := ha.1
    have pos2 : c > 0 := hc.1
    have pos3 : a * c > 0 := by positivity
    have h16 : Real.log (a ^ 2) = Real.log ((a * c) ^ (Real.logb c b)) := by
      have h17 : Real.log (a ^ 2) = 2 * Real.log a := by
        simp [Real.log_pow]
        <;> linarith
      have h18 : Real.log ((a * c) ^ (Real.logb c b)) = Real.logb c b * Real.log (a * c) := by
        rw [Real.log_rpow]
        all_goals
          try { positivity }
          try { linarith }
      have h19 : Real.log (a * c) = Real.log a + Real.log c := by
        rw [Real.log_mul (by linarith) (by linarith)]
      have h20 : Real.logb c b = Real.log b / Real.log c := by
        field_simp [Real.logb]

      rw [h17, h18, h19, h20]
      have hb2 : Real.log b ≠ 0 := hb2
      have hc2 : Real.log c ≠ 0 := hc2
      have ha2 : Real.log a ≠ 0 := ha2
      field_simp [hb2, hc2, show Real.log c ≠ 0 by exact hc2, show Real.log b ≠ 0 by exact hb2]
      <;> nlinarith [show (Real.log c + Real.log a) * Real.log b = 2 * (Real.log a * Real.log c) from by
        have h5 : Real.log 2018 * (1 / Real.log a + 1 / Real.log c) = 2 * Real.log 2018 / Real.log b := by
          field_simp [ha2, hc2, hb2] at h ⊢
          nlinarith
        have h7 : Real.log 2018 > 0 := h4
        have h8 : Real.log 2018 ≠ 0 := by linarith
        have eq1 : Real.log 2018 * (1 / Real.log a + 1 / Real.log c) = 2 * Real.log 2018 / Real.log b := h5
        have eq4 : 1 / Real.log a + 1 / Real.log c = 2 / Real.log b := by
          apply (mul_left_inj' (show Real.log 2018 ≠ 0 by linarith)).mp
          field_simp [hb2] at eq1 ⊢
          nlinarith
        field_simp [hb2] at eq4 ⊢
        <;> nlinarith [eq4]
      ]
    have pos4 : (a * c) ^ (Real.logb c b) > 0 := by positivity
    have pos5 : a ^ 2 > 0 := by positivity
    have h110 : a ^ 2 = (a * c) ^ (Real.logb c b) := by
      apply Real.log_injOn_pos (Set.mem_Ioi.mpr pos5) (Set.mem_Ioi.mpr pos4) h16
      all_goals try { tauto }
      all_goals try { linarith }
      all_goals try { tauto }
      all_goals try { positivity }
    exact h110
  constructor
  · linarith [h9]
  · exact h100