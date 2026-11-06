import Mathlib

theorem algebra_19869 (invest : ℝ) (rate : ℝ) (time : ℝ) (hP : invest = 10000) (hr : rate = 0.1) (ht : time = 5)
    (h : invest * (1 + rate / 4) ^ (4 * time) = x) :
    (round (100 * x) : ℝ) * 100⁻¹ = 16386.16 := by
  rw [hP] at h
  rw [hr] at h
  rw [ht] at h
  have hx : x = (10000 : ℝ) * (1 + (0.1 : ℝ) / 4) ^ (4 * (5 : ℝ)) := by 
    linarith [h]
  rw [hx]
  norm_num [round_eq]
  <;> try {linarith}
  <;> try {norm_num}