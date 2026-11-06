import Mathlib

theorem algebra_277306 (o v : ℝ) (h : o / v = 3) (h' : (o / (2 * v)) = x) :
    x = 3 / 2 := by 
  have hv : v ≠ 0 := by
    by_contra h1
    have h2 : v = 0 := by linarith 
    rw [h2] at h
    norm_num at h 
  have h1 : o = 3 * v := by 
    have : v ≠ 0 := hv
    field_simp [hv] at h
    linarith 
  have h2 : o / (2 * v) = 3 / 2 := by 
    have : v ≠ 0 := hv
    rw [h1] 
    have : v ≠ 0 := hv
    field_simp [hv] 
    <;> ring 
  have h3 : x = 3 / 2 := by 
    linarith [h', h2] 
  exact h3