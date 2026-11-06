import Mathlib

theorem algebra_610867 {r b t: ℕ} (hr : r = b + 12) (htotal: r + b = t) (hposi: b/t = 1/(4:ℝ)) : (t = 24):= by
  have h1 : (b : ℝ) / (t : ℝ) = (1 : ℝ) / 4 := by
    exact_mod_cast hposi
  have h2 : (t : ℝ) ≠ 0 := by
    by_contra h
    rw [h] at h1
    norm_num at h1
  have h3 : (b : ℝ) ≠ 0 := by
    by_contra h
    rw [h] at h1
    field_simp [h2] at h1
    all_goals norm_num at h1
  have h4 : (4 * (b : ℝ) = (t : ℝ)) := by
    field_simp [h2] at h1
    linarith
  have h5 : 4 * b = t := by
    exact_mod_cast h4
  have h6 : r = b + 12 := by
    exact_mod_cast hr
  have h7 : r + b = t := by
    exact_mod_cast htotal
  have h8 : (b + 12 + b : ℕ) = t := by
    linarith [h6, h7]
  have h9 : b = 6 := by
    omega
  have h10 : t = 24 := by
    omega
  exact_mod_cast h10