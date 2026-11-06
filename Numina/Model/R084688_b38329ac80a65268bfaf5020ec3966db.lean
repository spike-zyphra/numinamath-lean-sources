import Mathlib

theorem inequalities_119436 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x + y > 2) :
    (1 + y) / x < 2 ∨ (1 + x) / y < 2 := by
  by_contra h
  push_neg at h
  have h1 : (1 + y) / x ≥ 2 := by linarith
  have h2 : (1 + x) / y ≥ 2 := by linarith
  
  have h3 : 1 + y ≥ 2 * x := by
    have pos1 : 0 < x := hx
    apply (le_div_iff₀ pos1).mp at h1
    linarith
  
  have h4 : 1 + x ≥ 2 * y := by
    have pos2 : 0 < y := hy
    apply (le_div_iff₀ pos2).mp at h2
    linarith
  
  linarith