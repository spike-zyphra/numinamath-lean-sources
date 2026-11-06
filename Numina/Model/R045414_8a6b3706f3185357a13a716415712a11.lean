import Mathlib

theorem algebra_242690 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : (x * 0.6) / (y * 0.4) = x / y * (1 + z / 100)) :
    z = 50 := by
  have eq1 : (x * 0.6) / (y * 0.4) = (0.6 / 0.4) * (x / y) := by
    field_simp [hy, hx]
    <;> ring_nf
  have eq2 : (x * 0.6) / (y * 0.4) = (1.5 : ℝ) * (x / y) := by
    rw [eq1]
    norm_num
  have h1 : x / y ≠ 0 := by
    apply div_ne_zero 
    exact hx
    exact hy
  rw [eq2] at h
  have eq3 : (1.5 : ℝ) * (x / y) - (x / y) * (1 + z / 100) = 0 := by
    linarith 
  have eq4 : (x / y) * ((1.5 : ℝ) - (1 + z / 100)) = 0 := by
    ring_nf at eq3 ⊢
    linarith
  cases' (mul_eq_zero.mp eq4) with h5 h6
  · -- h5 : x / y = 0
    exfalso
    apply h1
    exact h5
  · -- h6 : (1.5 : ℝ) - (1 + z / 100) = 0
    norm_num at h6 
    linarith 
  all_goals tauto