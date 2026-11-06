import Mathlib

open Real

lemma lemma_1 (x : ℝ) (hx : 0 < x ∧ x < 1) :
    x / (1 - x ^ 2) ≥ 3 * sqrt 3 / 2 * x ^ 2 := by
  have h0 : 0 < x := hx.1
  have h1 : x < 1 := hx.2
  have h2 : 0 < 1 - x^2 := by
    nlinarith
  have hx2 : x / (1 - x^2) - 3 * Real.sqrt 3 / 2 * x^2 ≥ 0 := by
    have hx3 : x / (1 - x^2) - 3 * Real.sqrt 3 / 2 * x^2 = (2 * x - 3 * Real.sqrt 3 * x^2 * (1 - x^2)) / (2 * (1 - x^2)) := by
      field_simp
      ring
    rw [hx3] at *
    have hx5 : 2 * x - 3 * Real.sqrt 3 * x^2 * (1 - x^2) ≥ 0 := by
      have h4 : x * (2 - 3 * Real.sqrt 3 * x * (1 - x^2)) ≥ 0 := by
        have hx4 : 0 < x := h0
        have hx5 : 2 - 3 * Real.sqrt 3 * x * (1 - x^2) ≥ 0 := by
          nlinarith [sq_nonneg (x^2 - 1/3), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), sq_nonneg (x * Real.sqrt 3 - 1), sq_nonneg (x^2 - 1/3), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
        nlinarith
      linarith
    have hx6 : 0 < (2 * (1 - x^2) : ℝ) := by
      nlinarith
    have hx8 : (2 * x - 3 * Real.sqrt 3 * x^2 * (1 - x^2) ) / (2 * (1 - x^2)) ≥ 0 := by
      apply div_nonneg
      linarith
      nlinarith
    linarith
  linarith


theorem inequalities_602184 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x^2 + y^2 + z^2 = 1) :
    x / (1 - x^2) + y / (1 - y^2) + z / (1 - z^2) ≥ 3 * sqrt 3 / 2 := by
  have hx2 : 0 < x := hx
  have hy2 : 0 < y := hy
  have hz2 : 0 < z := hz
  have hx1 : 0 < 1 - x^2 := by
    nlinarith [sq_nonneg (y), sq_nonneg (z), h, sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz]
  have hy1 : 0 < 1 - y^2 := by
    nlinarith [sq_nonneg (x), sq_nonneg (z), h, sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz]
  have hz1 : 0 < 1 - z^2 := by
    nlinarith [sq_nonneg (x), sq_nonneg (y), h, sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz]
  have h1 : x / (1 - x^2) ≥ 3 * sqrt 3 / 2 * x^2 := by
    apply lemma_1
    constructor
    · linarith
    · nlinarith
  have h2 : y / (1 - y^2) ≥ 3 * sqrt 3 / 2 * y^2 := by
    apply lemma_1
    constructor
    · linarith
    · nlinarith
  have h3 : z / (1 - z^2) ≥ 3 * sqrt 3 / 2 * z^2 := by
    apply lemma_1
    constructor
    · linarith
    · nlinarith
  have h5 : 3 * sqrt 3 / 2 * x^2 + 3 * sqrt 3 / 2 * y^2 + 3 * sqrt 3 / 2 * z^2 = 3 * sqrt 3 / 2 * (x^2 + y^2 + z^2) := by
    ring
  have h6 : 3 * sqrt 3 / 2 * (x^2 + y^2 + z^2) = 3 * Real.sqrt 3 / 2 := by
    rw [show x^2 + y^2 + z^2 = 1 by linarith [h]]
    all_goals
      nlinarith
  linarith [h1, h2, h3, h5, h6, h, sq_nonneg (x^2 - 1/3), sq_nonneg (y^2 - 1/3), sq_nonneg (z^2 - 1/3)]