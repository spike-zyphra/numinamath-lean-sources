import Mathlib

open Real

theorem inequalities_110599 (a b : ℝ) (ha : 1 < a) (hb : a < b)
    (x y : ℝ) (hx : a < x) (hy : x < b) (hxy : y ∈ Set.Ioo a b) :
    logb x ((a + b) * y - a * b) * logb y ((a + b) * x - a * b) ≥ 4 := by
  rcases hxy with ⟨hy1, hy2⟩
  have h1 : 0 < x := by linarith
  have h2 : 0 < y := by linarith
  have h10 : (a + b) * y - a * b > 0 := by
    nlinarith
  have h11 : (a + b) * x - a * b > 0 := by
    nlinarith
  have h14 : log x > 0 := by
    apply log_pos
    linarith
  have h15 : log y > 0 := by
    apply log_pos
    linarith
  have h12 : logb x ((a + b) * y - a * b) = (log ((a + b) * y - a * b) ) / (log x) := by
    field_simp [logb]
  have h13 : logb y ((a + b) * x - a * b) = (log ((a + b) * x - a * b) ) / (log y) := by
    field_simp [logb]
  rw [h12, h13]
  have h16 : log ((a + b) * y - a * b) * log ((a + b) * x - a * b) ≥ 4 * (log x * log y) := by
    have h19 : log ((a + b) * y - a * b) ≥ 2 * log y := by
      have h19 : ( (a + b) * y - a * b ) ≥ y ^ 2 := by
        nlinarith [sq_nonneg (y - b), sq_nonneg (a - y), sq_nonneg (a - b), sq_nonneg (y - x)]
      have h20 : log ((a + b) * y - a * b) ≥ log (y ^ 2) := by
        apply Real.log_le_log
        all_goals nlinarith
      have h21 : log (y ^ 2) = 2 * log y := by
        simp [log_pow]
      linarith [h20, h21]
    have h20 : log ((a + b) * x - a * b) ≥ 2 * log x := by
      have h21 : ( (a + b) * x - a * b ) ≥ x ^ 2 := by
        nlinarith [sq_nonneg (x - b), sq_nonneg (a - x), sq_nonneg (a - b), sq_nonneg (x - y)]
      have h22 : log ((a + b) * x - a * b) ≥ log (x ^ 2) := by
        apply Real.log_le_log
        all_goals nlinarith
      have h23 : log (x ^ 2) = 2 * log x := by
        simp [log_pow]
      linarith [h22, h23]
    nlinarith [h19, h20, mul_pos (show log x > 0 by nlinarith) (show log y > 0 by nlinarith), sq_nonneg (log ((a + b) * y - a * b) - 2 * log y), sq_nonneg (log ((a + b) * x - a * b) - 2 * log x)]
  have h24 : (log ((a + b) * y - a * b) / log x) * (log ((a + b) * x - a * b) / log y) ≥ 4 := by
    have h25 : log x > 0 := h14
    have h26 : log y > 0 := h15
    have h27 : log ((a + b) * y - a * b) * log ((a + b) * x - a * b) ≥ 4 * (log x * log y) := h16
    have h28 : (log ((a + b) * y - a * b) / log x) * (log ((a + b) * x - a * b) / log y) = (log ((a + b) * y - a * b) * log ((a + b) * x - a * b)) / (log x * log y) := by
      field_simp
    rw [h28]
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  linarith [h24]