import Mathlib

theorem algebra_82891 {A H S M E : ℕ} {dX dY dT : ℝ}
    (hA : 0 < A) (hH : 0 < H) (hS : 0 < S) (hM : 0 < M) (hE : 0 < E)
    (hA1 : A ≠ H) (hA2 : A ≠ S) (hA3 : A ≠ M) (hA4 : A ≠ E)
    (hH2 : H ≠ S) (hH3 : H ≠ M) (hH4 : H ≠ E)
    (hS1 : S ≠ M) (hS2 : S ≠ E)
    (hM1 : M ≠ E)
    (hX1 : 0 < dX) (hY1 : dX < dY)
    (hT1 : A * dX + H * dY = dT)
    (hT2 : S * dX + M * dY = dT)
    (hT3 : E * dX = dT) :
    E = (A * M - H * S : ℝ) / (M - H) := by

  have hdX : dX = dT / E := by
    rw [hT3.symm]
    field_simp
  rw [hdX] at hT1 hT2
  field_simp at hT1 hT2

  have hYT₁ : dY / dT = (E - A : ℝ) / (E * H) := by
    rw [div_eq_div_iff]
    linarith
    intro hT
    -- Prove that dT ≠ 0
    rw [hT] at hdX
    simp at hdX
    linarith
    -- Prove that ↑E * ↑H ≠ 0
    field_simp

  have hYT₂ : dY / dT = (E - S: ℝ) / (E * M) := by
    rw [div_eq_div_iff]
    linarith
    intro hT
    -- Prove that dT ≠ 0
    rw [hT] at hdX
    simp at hdX
    linarith
    -- Prove that ↑E * ↑M ≠ 0
    field_simp

  rw [hYT₂, div_eq_div_iff] at hYT₁
  rw [mul_comm (E : ℝ), mul_comm (E : ℝ), ←mul_assoc, ←mul_assoc] at hYT₁
  simp at hYT₁
  rw [or_iff_left (by linarith)] at hYT₁
  rw [eq_div_iff]
  linarith
  -- Prove that ↑M - ↑H ≠ 0
  apply sub_ne_zero_of_ne
  simp
  exact hH3.symm
  repeat field_simp
