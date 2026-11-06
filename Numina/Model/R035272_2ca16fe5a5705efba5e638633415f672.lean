import Mathlib

theorem algebra_311023 {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x + 1 / y = 1) (hyz : y + 1 / z = 1) :
    x * y * z = -1 := by
  have eq1 : x = 1 - 1 / y := by linarith
  have eq2 : 1 / z = 1 - y := by linarith [hyz]
  have hne : 1 - y ≠ 0 := by
    by_contra h
    have h1 : 1 - y = 0 := by linarith
    have h2 : 1 / z = 0 := by linarith [eq2, h1]
    have h3 : z ≠ 0 := hz
    field_simp [hz] at h2 ⊢
    all_goals linarith
  have eq3 : z = 1 / (1 - y) := by
    have hne' : 1 - y ≠ 0 := hne
    field_simp [hz, hne'] at eq2 ⊢
    all_goals linarith
  have eq4 : x * y = y - 1 := by
    rw [eq1]
    field_simp [hy]
    <;> linarith
  calc
    x * y * z = (x * y) * z := by ring
    _ = (y - 1) * z := by rw [eq4]
    _ = (y - 1) * (1 / (1 - y)) := by rw [eq3]
    _ = -1 := by 
      have hne' : 1 - y ≠ 0 := hne
      field_simp [hne']
      <;> ring_nf
      <;> linarith