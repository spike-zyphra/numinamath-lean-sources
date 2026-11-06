import Mathlib

theorem algebra_285823 {a b : ℝ} (ha : (21.4 : ℝ)^a = 100) (hb : (0.00214 : ℝ)^b = 100) :
    1 / a - 1 / b = 2 := by
  have ha1 : a ≠ 0 := by
    by_contra h
    rw [h] at ha
    norm_num at ha
  have hb1 : b ≠ 0 := by
    by_contra h
    rw [h] at hb
    norm_num at hb
  have h1 : a * (Real.log (21.4 : ℝ)) = Real.log (100 : ℝ) := by
    have h2 : (21.4 : ℝ) ^ a = 100 := ha
    have h3 : Real.log ((21.4 : ℝ) ^ a) = Real.log (100 : ℝ) := by
      rw [h2]
    rw [Real.log_rpow] at h3
    all_goals linarith
  have h2 : b * (Real.log (0.00214 : ℝ)) = Real.log (100 : ℝ) := by
    have h3 : (0.00214 : ℝ) ^ b = 100 := hb
    have h4 : Real.log ((0.00214 : ℝ) ^ b) = Real.log (100 : ℝ) := by
      rw [h3]
    rw [Real.log_rpow] at h4
    all_goals linarith
  have ha2 : 1 / a = Real.log (21.4 : ℝ) / Real.log (100 : ℝ) := by
    have ha3 : a ≠ 0 := ha1
    field_simp [ha3]
    linarith [h1]
  have hb2 : 1 / b = Real.log (0.00214 : ℝ) / Real.log (100 : ℝ) := by
    have hb3 : b ≠ 0 := hb1
    field_simp [hb3]
    linarith [h2]
  rw [ha2, hb2]
  have h3 : Real.log (21.4 : ℝ) - Real.log (0.00214 : ℝ) = 4 * Real.log (10 : ℝ) := by
    have h4 : Real.log (21.4 : ℝ) - Real.log (0.00214 : ℝ) = Real.log ((21.4 : ℝ) / (0.00214 : ℝ)) := by
      rw [Real.log_div (by norm_num) (by norm_num)]
    have h5 : (21.4 : ℝ) / (0.00214 : ℝ) = (10000 : ℝ) := by norm_num
    rw [h4, h5]
    have h6 : Real.log (10000 : ℝ) = Real.log (10 ^ 4 : ℝ) := by
      norm_num
    rw [h6]
    have h7 : Real.log (10 ^ 4 : ℝ) = 4 * Real.log (10 : ℝ) := by
      simp [Real.log_pow]
    rw [h7]
  have h4 : Real.log (100 : ℝ) = 2 * Real.log (10 : ℝ) := by
    calc
      Real.log (100 : ℝ) = Real.log (10 ^ 2 : ℝ) := by
        norm_num
      _ = 2 * Real.log (10 : ℝ) := by
        simp [Real.log_pow]
  have h51 : Real.log (100 : ℝ) ≠ 0 := by
    have h52 : Real.log (100 : ℝ) > 0 := by
      apply Real.log_pos
      all_goals norm_num
    linarith [h52]
  have h53 : Real.log (21.4 : ℝ) / Real.log (100 : ℝ) - Real.log (0.00214 : ℝ) / Real.log (100 : ℝ) =
      (Real.log (21.4 : ℝ) - Real.log (0.00214 : ℝ)) / Real.log (100 : ℝ) := by
    field_simp [h51]
    <;> ring
  rw [h53]
  rw [h3, h4]
  have h8 : Real.log (10 : ℝ) ≠ 0 := by
    have h81 : Real.log (10 : ℝ) > 0 := by
      apply Real.log_pos
      all_goals norm_num
    linarith [h81]
  field_simp [h8]
  <;> ring