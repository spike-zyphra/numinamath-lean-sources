import Mathlib

theorem algebra_320480 {r h : ℝ} (hr : r > 0) (hh : h > 0)
    (hvol : π * r^2 * h = 1) (hsurf : 2 * π * r * h + 2 * π * r^2 = 12) :
    1 / r + 1 / h = 6 := by
  have eq1 : π * r * (r + h) = 6 := by 
    linarith 
  have eq2 : π * r^2 * h = 1 := by 
    linarith 
  have eq3 : (h + r) / (r * h) = 6 := by 
    have h1 : π * r ^ 2 * h ≠ 0 := by 
      have hr1 : r > 0 := hr
      have hh1 : h > 0 := hh 
      have h2 : r * h > 0 := by nlinarith 
      have h3 : r ^ 2 * h > 0 := by nlinarith 
      have h4 : π * r ^ 2 * h > 0 := by nlinarith [Real.pi_pos] 
      linarith [show π * r ^ 2 * h ≠ 0 by nlinarith]
    have h4 : (π * r * (r + h)) / (π * r^2 * h) = (6 / 1 : ℝ) := by 
      rw [eq1, eq2] 
      all_goals norm_num 
    have h5 : (π * r * (r + h)) / (π * r^2 * h) = (h + r) / (r * h) := by
      have h11 : r ≠ 0 := by linarith 
      have h12 : h ≠ 0 := by linarith 
      have hp1 : π ≠ 0 := by
        by_contra hpi 
        have h14 : π * r ^ 2 * h ≠ 0 := h1 
        rw [hpi] at h14 
        have h21 : (0) * r ^ 2 * h = 0 := by 
          simp 
        rw [h21] at h14
        all_goals try { contradiction } 
      field_simp [h11, h12, hp1] 
      <;> ring
    rw [h5] at h4 
    norm_num at h4 ⊢
    linarith
  have eq4 : 1 / r + 1 / h = 6 := by 
    have eq3' : (h + r) / (r * h) = 6 := eq3
    have eq4' : (h + r) / (r * h) = 1 / r + 1 / h := by 
      field_simp [show r ≠ 0 by linarith, show h ≠ 0 by linarith]
      <;> ring 
    linarith [eq3', eq4']
  exact eq4