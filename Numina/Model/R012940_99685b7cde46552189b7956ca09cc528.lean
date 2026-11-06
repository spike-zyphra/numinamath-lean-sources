import Mathlib

theorem inequalities_51103 (M m : ℝ) (hM : ∃ x, 4 * x * (x - 5) ≤ 375 ∧ x = M) (hm : ∃ x, 4 * x * (x - 5) ≤ 375 ∧ x = m)
    (hMub : ∀ x, 4 * x * (x - 5) ≤ 375 → x ≤ M) (hmub : ∀ x, 4 * x * (x - 5) ≤ 375 → x ≥ m) :
    M - m = 20 := by
  have h1 : 4 * (-7.5 : ℝ) * ((-7.5 : ℝ) - 5) ≤ 375 := by norm_num
  have h2 : 4 * (12.5 : ℝ) * ((12.5 : ℝ) - 5) ≤ 375 := by norm_num
  have h3 : (12.5 : ℝ) ≤ M := by
    apply hMub
    linarith
  have h4 : (-7.5 : ℝ) ≥ m := by
    apply hmub
    linarith
  rcases hM with ⟨x, hx1, hx2⟩
  have h5 : 4 * M * (M - 5) ≤ 375 := by
    rw [show x = M by linarith [hx2]] at hx1
    linarith
  rcases hm with ⟨y, hy1, hy2⟩
  have h6 : 4 * m * (m - 5) ≤ 375 := by
    rw [show y = m by linarith [hy2]] at hy1
    linarith
  have h7 : M = 12.5 := by
    nlinarith [h5, hMub 12.5 (by nlinarith)]
  have h8 : m = -7.5 := by
    nlinarith [h6, hmub (-7.5) (by nlinarith)]
  rw [h7, h8]
  norm_num