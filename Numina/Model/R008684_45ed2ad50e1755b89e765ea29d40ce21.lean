import Mathlib

theorem algebra_19717 (x : ℝ) (h : (1 + 6 / 100)^5 * x = 100000) :
    round x = 74726 := by 
  have h1 : x = 100000 / (1 + 6 / 100 : ℝ)^5 := by 
    field_simp 
    linarith 
  rw [h1]
  norm_num [round_eq]
  <;> try { norm_num }