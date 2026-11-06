import Mathlib

theorem algebra_231505 (v t : ℝ) (ht : t > 0) (h : 40 / v = t ∧ 45 / (v - 1) = t) :
    d = 54 := by
  rcases h with ⟨h1, h2⟩
  have h3 : v ≠ 0 := by
    by_contra h4
    rw [h4] at h1
    norm_num at h1
    all_goals linarith
  have h4 : v - 1 ≠ 0 := by
    by_contra h5
    rw [h5] at h2
    norm_num at h2
    all_goals linarith
  have eq1 : 40 * (v - 1) = 45 * v := by
    have ht1 : 40 / v = t := by linarith
    have ht2 : 45 / (v - 1) = t := by linarith
    have ht_eq : t = 40 / v := by linarith
    have ht_eq2 : t = 45 / (v - 1) := by linarith
    rw [ht_eq] at ht_eq2
    field_simp [h3, h4] at ht_eq2 ⊢
    nlinarith
  have hv : v = -8 := by 
    linarith 
  have ht' : t < 0 := by 
    have ht_eq : t = 40 / v := by linarith 
    rw [ht_eq, hv]
    norm_num 
  linarith