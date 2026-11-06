import Mathlib

theorem algebra_325262 (m n p : ℝ) (hm : 0 < m) (hn : 0 < n) (hp : 0 < p)
    (h : m^2 + n^2 - p^2 = 0) :
    p / (m + n) ≥ Real.sqrt 2 / 2 := by
  have hp2 : p^2 = m^2 + n^2 := by linarith
  have h1 : 0 < m + n := by
    linarith
  have h2 : 2 * p^2 ≥ (m + n) ^ 2 := by
    have hp2 : p^2 = m^2 + n^2 := by linarith
    nlinarith [sq_nonneg (m - n)]
  have h3 : (p / (m + n)) ^ 2 ≥ 1 / 2 := by
    have h4 : (m + n) ^ 2 > 0 := by
      positivity
    have h5 : (p / (m + n)) ^ 2 = p^2 / (m + n) ^ 2 := by
      field_simp
    rw [h5]
    have h6 : p^2 = m^2 + n^2 := by linarith
    have h7 : 2 * (m ^ 2 + n ^ 2) ≥ (m + n) ^ 2 := by
      nlinarith [sq_nonneg (m - n)]
    have h8 : 2 * p^2 ≥ (m + n) ^ 2 := by
      rw [show p^2 = m^2 + n^2 by linarith]
      linarith [h7]
    have h9 : p^2 / (m + n) ^ 2 ≥ 1 / 2 := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith
    linarith
  have h4 : p / (m + n) ≥ Real.sqrt (1 / 2) := by
    have h5 : Real.sqrt ((p / (m + n)) ^ 2) ≥ Real.sqrt (1 / 2) := by
      apply Real.sqrt_le_sqrt
      linarith [h3]
    have h6 : Real.sqrt ((p / (m + n)) ^ 2) = p / (m + n) := by
      rw [Real.sqrt_sq (show 0 ≤ (p / (m + n) : ℝ) by
        have hp0 : 0 < p := hp
        have hm0 : 0 < m := hm
        have hn0 : 0 < n := hn
        have hmn0 : 0 < m + n := by linarith [hm0, hn0]
        have hfrac0 : 0 < p / (m + n) := by
          apply div_pos
          linarith
          linarith
        linarith
      )]
    linarith [h6, h5]
  have h5 : Real.sqrt (1 / 2) = Real.sqrt 2 / 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  rw [h5] at h4
  linarith