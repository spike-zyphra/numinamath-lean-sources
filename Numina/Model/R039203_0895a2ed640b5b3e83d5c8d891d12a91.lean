import Mathlib

theorem algebra_134501 {a b c x1 x2 : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hroots : x1 = 2022 * x2 ∧ a * x1 ^ 2 + b * x1 + c = 0 ∧ a * x2 ^ 2 + b * x2 + c = 0) :
    2023 * a * c / b ^ 2 = 2022 / 2023 := by

  rcases hroots with ⟨hx1x2, h1, h2⟩

  have hx2ne : x2 ≠ 0 := by
    by_contra h
    have h2' : x2 = 0 := by linarith
    rw [h2'] at h2
    have hc' : c = 0 := by
      nlinarith
    contradiction

  have eq1 : a * (2022 * x2) ^ 2 + b * (2022 * x2) + c - (a * x2 ^ 2 + b * x2 + c) = 0 := by
    rw [show x1 = 2022 * x2 by linarith] at h1
    linarith [h1, h2]

  have eq2 : a * x2 ^ 2 * (2022^2 - 1) + b * x2 * (2022 - 1) = 0 := by
    ring_nf at eq1 ⊢
    <;> nlinarith

  have eq3 : a * x2 * (2022^2 - 1) + b * (2022 - 1) = 0 := by
    apply (mul_left_inj' hx2ne).mp
    linarith

  have eq4 : b = -a * x2 * 2023 := by
    have h5 : (2022 ^ 2 - 1 : ℝ) = (2022 - 1 : ℝ) * (2022 + 1 : ℝ) := by
      ring_nf
    rw [h5] at eq3
    have h6 : (2022 - 1 : ℝ) = (2021 : ℝ) := by
      norm_num
    rw [h6] at eq3
    have h7 : (2022 + 1 : ℝ) = (2023 : ℝ) := by
      norm_num
    rw [h7] at eq3
    have eq5 : a * x2 * (2021 * (2023 : ℝ)) + b * (2021 : ℝ) = 0 := by
      ring_nf at eq3 ⊢
      <;> linarith
    have h8 : (2021 : ℝ) ≠ 0 := by
      norm_num
    have eq6 : a * x2 * (2023 : ℝ) + b = 0 := by
      apply (mul_left_inj' h8).mp
      linarith
    nlinarith

  have eq7 : c = 2022 * a * x2 ^ 2 := by
    have eq8 : a * x2 ^ 2 + b * x2 + c = 0 := by
      linarith [h2]
    rw [eq4] at eq8
    nlinarith

  have eq8 : b ^ 2 = a ^ 2 * x2 ^ 2 * (2023 ^ 2) := by
    rw [eq4]
    ring_nf

  have eq9 : 2023 * a * c = 2023 * 2022 * a ^ 2 * x2 ^ 2 := by
    rw [eq7]
    ring_nf

  have eq10 : a * x2 ≠ 0 := by
    apply mul_ne_zero
    exact ha
    exact hx2ne

  have h4 : a ^ 2 * x2 ^ 2 ≠ 0 := by
    apply mul_ne_zero
    · -- Show a ^ 2 ≠ 0
      apply pow_ne_zero 2
      exact ha
    · -- Show x2 ^ 2 ≠ 0
      apply pow_ne_zero 2
      exact hx2ne

  rw [eq9, eq8]
  field_simp [h4]
  <;> ring_nf <;> nlinarith