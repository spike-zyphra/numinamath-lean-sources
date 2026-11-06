import Mathlib

theorem algebra_195557 {x p q r : ℝ} (hx : 0 < x) (hpqr : 0 < p ∧ p ≠ 1 ∧ 0 < q ∧ q ≠ 1 ∧ 0 < r ∧ r ≠ 1)
    (h₁ : Real.logb p x = 2) (h₂ : Real.logb q x = 3) (h₃ : Real.logb r x = 6) :
    Real.logb (p * q * r) x = 1 := by

  rcases hpqr with ⟨hp_pos, hp_ne1, hq_pos, hq_ne1, hr_pos, hr_ne1⟩

  have h1 : Real.logb p x = (Real.log x) / (Real.log p) := by
    field_simp [Real.logb]

  have eq1 : (Real.log x) / (Real.log p) = 2 := by
    rw [h1] at h₁
    linarith

  have h4 : Real.log p ≠ 0 := by
    have hp1 : p > 0 := hp_pos
    have hp2 : p ≠ 1 := hp_ne1
    exact Real.log_ne_zero_of_pos_of_ne_one hp1 hp2

  have eq2 : Real.log x = 2 * Real.log p := by
    field_simp [h4] at eq1 ⊢
    linarith

  have h5 : Real.logb q x = (Real.log x) / (Real.log q) := by
    field_simp [Real.logb]

  have h8 : Real.log q ≠ 0 := by
    have hq1 : q > 0 := hq_pos
    have hq2 : q ≠ 1 := hq_ne1
    exact Real.log_ne_zero_of_pos_of_ne_one hq1 hq2

  have eq3 : (Real.log x) / (Real.log q) = 3 := by
    rw [h5] at h₂
    linarith

  have eq4 : Real.log x = 3 * Real.log q := by
    field_simp [h8] at eq3 ⊢
    linarith

  have h6 : Real.logb r x = (Real.log x) / (Real.log r) := by
    field_simp [Real.logb]

  have h9 : Real.log r ≠ 0 := by
    have hr1 : r > 0 := hr_pos
    have hr2 : r ≠ 1 := hr_ne1
    exact Real.log_ne_zero_of_pos_of_ne_one hr1 hr2

  have eq5 : (Real.log x) / (Real.log r) = 6 := by
    rw [h6] at h₃
    linarith

  have eq6 : Real.log x = 6 * Real.log r := by
    field_simp [h9] at eq5 ⊢
    linarith

  have eq7 : Real.log (p * q * r) = Real.log p + Real.log q + Real.log r := by
    simp [Real.log_mul, hp_pos.ne.symm, hq_pos.ne.symm, hr_pos.ne.symm]

  have eq8 : Real.log q = (2 / 3) * Real.log p := by
    have eq9 : 2 * Real.log p = 3 * Real.log q := by
      linarith [eq2, eq4]
    linarith

  have eq9 : Real.log r = (1 / 3) * Real.log p := by
    have eq10 : 2 * Real.log p = 6 * Real.log r := by
      linarith [eq2, eq6]
    linarith

  have eq10 : Real.log (p * q * r) = 2 * Real.log p := by
    rw [eq7]
    rw [eq8, eq9]
    linarith

  have h11 : Real.logb (p * q * r) x = (Real.log x) / (Real.log (p * q * r)) := by
    field_simp [Real.logb]

  rw [h11]
  rw [eq10]
  have h12 : Real.log p ≠ 0 := h4
  field_simp [h12]
  <;> nlinarith [eq2]