import Mathlib

theorem algebra_2333 {a : ℝ} (ha : a ≠ 0) (h : (1 + a / 100) * (1 - x) = 1) :
    x = a / (100 + a) := by
  have h1 : 100 + a ≠ 0 := by
    by_contra h2
    have h2' : a = -100 := by linarith
    rw [h2'] at h
    norm_num at h
  have eq2 : x = a / (100 + a) := by
    have h3 : (1 + a / (100 : ℝ)) = (100 + a) / 100 := by
      field_simp
      <;> linarith
    rw [h3] at h
    have h4 : (1 - x) = 100 / (100 + a) := by
      field_simp [(show 100 + a ≠ 0 by assumption)] at h ⊢
      <;> nlinarith
    have h5 : x = 1 - (100 / (100 + a)) := by
      linarith
    rw [h5]
    field_simp [(show 100 + a ≠ 0 by assumption)]
    <;> nlinarith
  exact eq2