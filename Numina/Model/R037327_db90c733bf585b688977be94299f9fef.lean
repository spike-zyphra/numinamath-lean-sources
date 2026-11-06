import Mathlib

open Real

theorem inequalities_600066 (x : Fin 4 → ℝ) (hx : ∀ i, 0 < x i) :
    1 / 2 * ((x 0 + x 1) / (x 1 + x 2) + (x 1 + x 2) / (x 2 + x 3) +
      (x 2 + x 3) / (x 3 + x 0) + (x 3 + x 0) / (x 0 + x 1)) ≤
    (x 0) / (x 1 + x 2) + (x 1) / (x 2 + x 3) + (x 2) / (x 3 + x 0) +
    (x 3) / (x 0 + x 1) := by

  have hx1 : 0 < x 1 := hx 1
  have hx2 : 0 < x 2 := hx 2
  have hx3 : 0 < x 3 := hx 3
  have hx0 : 0 < x 0 := hx 0

  have h1 : 0 < x 1 + x 2 := by linarith
  have h2 : 0 < x 2 + x 3 := by linarith
  have h3 : 0 < x 3 + x 0 := by linarith
  have h4 : 0 < x 0 + x 1 := by linarith

  have h6 : (x 0) / (x 1 + x 2) + (x 1) / (x 2 + x 3) + (x 2) / (x 3 + x 0) +
      (x 3) / (x 0 + x 1) - 1 / 2 * ((x 0 + x 1) / (x 1 + x 2) + (x 1 + x 2) / (x 2 + x 3) +
        (x 2 + x 3) / (x 3 + x 0) + (x 3 + x 0) / (x 0 + x 1)) ≥ 0 := by
    have ha1 : 0 < (x 1 + x 2) := by linarith
    have ha2 : 0 < (x 2 + x 3) := by linarith
    have ha3 : 0 < (x 3 + x 0) := by linarith
    have ha4 : 0 < (x 0 + x 1) := by linarith

    have eq6 : (x 0) / (x 1 + x 2) + (x 1) / (x 2 + x 3) + (x 2) / (x 3 + x 0) +
        (x 3) / (x 0 + x 1) - 1 / 2 * ((x 0 + x 1) / (x 1 + x 2) + (x 1 + x 2) / (x 2 + x 3) +
          (x 2 + x 3) / (x 3 + x 0) + (x 3 + x 0) / (x 0 + x 1)) =
          ((x 0) * (x 2 + x 3) * (x 3 + x 0) * (x 0 + x 1) +
          (x 1) * (x 1 + x 2) * (x 3 + x 0) * (x 0 + x 1) +
          (x 2) * (x 1 + x 2) * (x 2 + x 3) * (x 0 + x 1) +
          (x 3) * (x 1 + x 2) * (x 2 + x 3) * (x 3 + x 0) -
          1 / 2 * ((x 0 + x 1) * (x 2 + x 3) * (x 3 + x 0) * (x 0 + x 1) +
          (x 1 + x 2) * (x 1 + x 2) * (x 3 + x 0) * (x 0 + x 1) +
          (x 2 + x 3) * (x 1 + x 2) * (x 2 + x 3) * (x 0 + x 1) +
          (x 3 + x 0) * (x 1 + x 2) * (x 2 + x 3) * (x 3 + x 0))) / ((x 1 + x 2) * (x 2 + x 3) * (x 3 + x 0) * (x 0 + x 1)) := by
      field_simp
      ring
    rw [eq6] at *
    have hx7 : ((x 0) * (x 2 + x 3) * (x 3 + x 0) * (x 0 + x 1) +
        (x 1) * (x 1 + x 2) * (x 3 + x 0) * (x 0 + x 1) +
        (x 2) * (x 1 + x 2) * (x 2 + x 3) * (x 0 + x 1) +
        (x 3) * (x 1 + x 2) * (x 2 + x 3) * (x 3 + x 0) -
        1 / 2 * ((x 0 + x 1) * (x 2 + x 3) * (x 3 + x 0) * (x 0 + x 1) +
        (x 1 + x 2) * (x 1 + x 2) * (x 3 + x 0) * (x 0 + x 1) +
        (x 2 + x 3) * (x 1 + x 2) * (x 2 + x 3) * (x 0 + x 1) +
        (x 3 + x 0) * (x 1 + x 2) * (x 2 + x 3) * (x 3 + x 0))) ≥ 0 := by
      nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 - x 2), sq_nonneg (x 0 - x 3), sq_nonneg (x 1 - x 2), sq_nonneg (x 1 - x 3), sq_nonneg (x 2 - x 3),
                  sq_nonneg (x 0 + x 1 - x 2 - x 3), sq_nonneg (x 1 + x 2 - x 3 - x 0),
                  mul_pos hx0 hx1, mul_pos hx0 hx2, mul_pos hx0 hx3,
                  mul_pos hx1 hx2, mul_pos hx1 hx3, mul_pos hx2 hx3]
    have hx8 : ((x 0) * (x 2 + x 3) * (x 3 + x 0) * (x 0 + x 1) +
        (x 1) * (x 1 + x 2) * (x 3 + x 0) * (x 0 + x 1) +
        (x 2) * (x 1 + x 2) * (x 2 + x 3) * (x 0 + x 1) +
        (x 3) * (x 1 + x 2) * (x 2 + x 3) * (x 3 + x 0) -
        1 / 2 * ((x 0 + x 1) * (x 2 + x 3) * (x 3 + x 0) * (x 0 + x 1) +
        (x 1 + x 2) * (x 1 + x 2) * (x 3 + x 0) * (x 0 + x 1) +
        (x 2 + x 3) * (x 1 + x 2) * (x 2 + x 3) * (x 0 + x 1) +
        (x 3 + x 0) * (x 1 + x 2) * (x 2 + x 3) * (x 3 + x 0))) / ((x 1 + x 2) * (x 2 + x 3) * (x 3 + x 0) * (x 0 + x 1)) ≥ 0 := by
      apply div_nonneg
      linarith [hx7]
      positivity
    linarith [hx8]
  linarith