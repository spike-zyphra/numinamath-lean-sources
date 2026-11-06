import Mathlib

theorem algebra_305326 {x a b c : ℝ} (ha : 0 < a ∧ a ≠ 1) (hb : 0 < b ∧ b ≠ 1)
    (hc : 0 < c ∧ c ≠ 1) (hx : 0 < x) (h₁ : Real.logb a x = 24) (h₂ : Real.logb b x = 40)
    (h₃ : Real.logb (a * b * c) x = 12) :
    Real.logb c x = 60 := by
  have h1 : Real.logb a x = Real.log x / Real.log a := by
    field_simp [Real.logb]
  have h2 : Real.logb b x = Real.log x / Real.log b := by
    field_simp [Real.logb]
  have h3 : Real.logb (a * b * c) x = Real.log x / Real.log (a * b * c) := by
    field_simp [Real.logb]
  have h4 : Real.logb c x = Real.log x / Real.log c := by
    field_simp [Real.logb]
  rw [h1] at h₁
  rw [h2] at h₂
  rw [h3] at h₃
  rw [h4] at *
  have ha1 : a > 0 := ha.1
  have ha2 : a ≠ 1 := ha.2
  have hb1 : b > 0 := hb.1
  have hb2 : b ≠ 1 := hb.2
  have hc1 : c > 0 := hc.1
  have hc2 : c ≠ 1 := hc.2
  have hloga_ne_zero : Real.log a ≠ 0 := by
    have ha1' : a > 0 := ha.1
    have ha2' : a ≠ 1 := ha.2
    exact Real.log_ne_zero_of_pos_of_ne_one ha1' ha2'
  have hlogb_ne_zero : Real.log b ≠ 0 := by
    have hb1' : b > 0 := hb.1
    have hb2' : b ≠ 1 := hb.2
    exact Real.log_ne_zero_of_pos_of_ne_one hb1' hb2'
  have hlogc_ne_zero : Real.log c ≠ 0 := by
    have hc1' : c > 0 := hc.1
    have hc2' : c ≠ 1 := hc.2
    exact Real.log_ne_zero_of_pos_of_ne_one hc1' hc2'
  have eq1 : Real.log x = 24 * Real.log a := by
    have hne : Real.log a ≠ 0 := hloga_ne_zero
    field_simp [hne] at h₁
    linarith
  have eq2 : Real.log x = 40 * Real.log b := by
    have hne : Real.log b ≠ 0 := hlogb_ne_zero
    field_simp [hne] at h₂
    linarith
  have hlogabc : Real.log (a * b * c) = Real.log a + Real.log b + Real.log c := by
    simp [Real.log_mul, ha1.ne.symm, hb1.ne.symm, hc1.ne.symm]
  have hlnx_ne_zero : Real.log x ≠ 0 := by
    by_contra h0
    have h0' : Real.log x = (0 : ℝ) := by linarith
    have eq1' : Real.log x = 24 * Real.log a := by
      have hne : Real.log a ≠ 0 := hloga_ne_zero
      field_simp [hne] at h₁
      linarith
    rw [h0'] at eq1'
    have h6 : Real.log a = 0 := by
      linarith
    have h7 : Real.log a ≠ 0 := hloga_ne_zero
    contradiction
  have eq4 : Real.log x = 12 * Real.log (a * b * c) := by
    have hne : Real.log (a * b * c) ≠ 0 := by
      by_contra h
      have h7 : Real.log (a * b * c) = 0 := by linarith [h]
      have h7' : Real.log a + Real.log b + Real.log c = 0 := by
        linarith [h7, hlogabc]
      have h0 : Real.log x / Real.log (a * b * c) = 12 := by linarith [h₃]
      field_simp [show Real.log (a * b * c) = (0 : ℝ) by linarith [h7]] at h0
      all_goals
        exfalso
        tauto
    field_simp [hne] at h₃
    linarith
  have eq5 : Real.log a = Real.log b + Real.log c := by
    rw [hlogabc] at eq4
    linarith [eq1, eq4]
  have eq3 : Real.log a = 5 / 3 * Real.log b := by
    linarith [eq1, eq2]
  have eq6 : Real.log c = 2 / 3 * Real.log b := by
    linarith [eq3, eq5]
  have h9 : Real.log x / Real.log c = 60 := by
    have hne4 : Real.log c ≠ 0 := hlogc_ne_zero
    have hlnx : Real.log x = 40 * Real.log b := eq2
    rw [eq6]
    have hlnb_ne_zero : Real.log b ≠ 0 := hlogb_ne_zero
    field_simp [show Real.log b ≠ 0 by assumption]
    <;> nlinarith
  linarith [h9]