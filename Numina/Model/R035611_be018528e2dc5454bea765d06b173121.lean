import Mathlib


theorem algebra_257334 {l1 l2 d1 d2 α1 α2 : ℝ}
    (hl1 : l1 > 0) (hl2 : l2 > 0) (hd1 : d1 > 0) (hd2 : d2 > 0)
    (hα1 : α1 > 0) (hα2 : α2 > 0)
    (h_center_invariant : ∀ t, t ≥ 0 → 
      (l2^2 * (1 + α2 * t)^2 * d2 / (1 + α2 * t) - l1^2 * (1 + α1 * t)^2 * d1 / (1 + α1 * t)) / 
      (2 * (l1 * (1 + α1 * t) * d1 / (1 + α1 * t) + l2 * (1 + α2 * t) * d2 / (1 + α2 * t))) =
      (l2^2 * d2 - l1^2 * d1) / (2 * (l1 * d1 + l2 * d2))) :
    l1 / l2 = √(d2 * α2 / (d1 * α1)) := by
  have eq1 := h_center_invariant 1 (by norm_num)
  have eq2 : l2^2 * (1 + α2 * (1 : ℝ))^2 * d2 / (1 + α2 * (1 : ℝ)) - l1^2 * (1 + α1 * (1 : ℝ))^2 * d1 / (1 + α1 * (1 : ℝ)) = l2^2 * (1 + α2) * d2 - l1^2 * (1 + α1) * d1 := by
    field_simp [(show (1 + α2 * (1 : ℝ)) ≠ 0 by positivity), (show (1 + α1 * (1 : ℝ)) ≠ 0 by positivity)]
    all_goals ring
  have eq3 : 2 * (l1 * (1 + α1 * (1 : ℝ)) * d1 / (1 + α1 * (1 : ℝ)) + l2 * (1 + α2 * (1 : ℝ)) * d2 / (1 + α2 * (1 : ℝ))) = 2 * (l1 * d1 + l2 * d2) := by 
    field_simp [(show (1 + α1 * (1 : ℝ)) ≠ 0 by positivity), (show (1 + α2 * (1 : ℝ)) ≠ 0 by positivity)]
    all_goals ring
  rw [eq2, eq3] at eq1
  have eq4 : l2^2 * (1 + α2) * d2 - l1^2 * (1 + α1) * d1 = l2^2 * d2 - l1^2 * d1 := by 
    have pos1 : l1 * d1 + l2 * d2 > 0 := by positivity
    have h1 : (l2^2 * (1 + α2) * d2 - l1^2 * (1 + α1) * d1) / (2 * (l1 * d1 + l2 * d2)) = (l2^2 * d2 - l1^2 * d1) / (2 * (l1 * d1 + l2 * d2)) := by
      linarith
    have pos2 : (2 * (l1 * d1 + l2 * d2)) ≠ 0 := by positivity
    field_simp at h1 ⊢
    all_goals nlinarith
  have eq5 : l2^2 * α2 * d2 = l1^2 * α1 * d1 := by
    nlinarith
  have eq6 : (l1 ^ 2) / (l2 ^ 2) = (d2 * α2) / (d1 * α1) := by
    have pos1 : l2^2 > 0 := by positivity
    have pos2 : d1 * α1 > 0 := mul_pos hd1 hα1
    field_simp
    nlinarith [eq5]
  have eq7 : l1 / l2 = Real.sqrt ((d2 * α2) / (d1 * α1)) := by
    have h1 : (l1 / l2) ^ 2 = (d2 * α2) / (d1 * α1) := by
      have h3 : (l1 / l2) ^ 2 = (l1 ^ 2) / (l2 ^ 2) := by field_simp
      rw [h3]
      linarith [eq6]
    have h2 : l1 / l2 ≥ 0 := by positivity
    have h3 : Real.sqrt ((l1 / l2) ^ 2) = Real.sqrt ((d2 * α2) / (d1 * α1)) := by 
      rw [h1]
    have h4 : Real.sqrt ((l1 / l2) ^ 2) = l1 / l2 := by 
      rw [Real.sqrt_sq (show 0 ≤ l1 / l2 by positivity)]
    linarith [h4, h3]
  linarith [eq7]