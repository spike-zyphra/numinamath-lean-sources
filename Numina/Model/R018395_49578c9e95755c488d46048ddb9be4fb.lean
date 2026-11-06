import Mathlib

theorem algebra_762 {x : ℝ} (hx : x * 1.18 = 56767) :
    round x = 48108 := by
  have hx2 : x = (56767 : ℝ) / 1.18 := by
    have h1 : (x : ℝ) * 1.18 = 56767 := hx
    field_simp
    linarith
  rw [hx2]
  norm_num [round_eq]
  all_goals norm_num
  <;> try { norm_num }
  <;> try { norm_num }