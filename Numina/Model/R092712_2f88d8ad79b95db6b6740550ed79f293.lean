import Mathlib

theorem algebra_262881 (p : ℝ) (hp : p > 0) (h : 200 / p = v) :
    v * 3.6 = 720 / p := by
  have hv : v = 200 / p := by
    field_simp at h ⊢
    linarith 
  rw [hv]
  field_simp
  <;> ring_nf <;> linarith