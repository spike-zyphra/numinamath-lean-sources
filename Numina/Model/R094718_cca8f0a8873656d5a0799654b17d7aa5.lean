import Mathlib

theorem algebra_176251 {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h1 : (5 * x + y) / (5 * x + y + x + y) = 2 * x / (5 * x + y + x + y))
    (h2 : (x + y) / (x + y + x + y) = 0.08) :
    x = 0.51 ∧ y = 0.11 := by 
  have h2_simp : (x + y) / (x + y + x + y) = (x + y) / (2 * (x + y)) := by 
    ring_nf
  have h2_simp' : (x + y) / (2 * (x + y)) = 1 / 2 := by 
    have h4 : 0 < x + y := by nlinarith
    field_simp
    <;> ring_nf
  rw [h2_simp] at h2
  rw [h2_simp'] at h2
  norm_num at h2
  all_goals try { 
    exfalso
    <;> norm_num at *
    <;> try { 
      linarith [show 0 < x from hx, show 0 < y from hy] 
    }
  }