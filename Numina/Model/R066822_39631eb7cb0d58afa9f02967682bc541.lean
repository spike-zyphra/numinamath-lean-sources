import Mathlib

theorem algebra_194701 (d t : ℝ) (ht : t = 1.4) (h : d / t = 30) (h' : d / (t - 12 / 60) = v) :
    v = 35 := by 
  have ht' : t = 1.4 := ht
  have ht_ne_zero : t ≠ (0 : ℝ) := by 
    rw [ht]
    norm_num
  have hd : d = 30 * t := by
    field_simp [ht_ne_zero] at h
    linarith
  rw [ht] at hd 
  have hd' : d = 42 := by
    norm_num at hd ⊢
    linarith
  have ht2 : t - 12 / 60 ≠ 0 := by
    rw [ht]
    norm_num
  have eq1 : v = d / (t - 12 / 60) := by
    rw [h']
    <;> try field_simp [ht2]
    all_goals linarith
  rw [eq1]
  rw [hd', ht]
  norm_num
  all_goals norm_num
  all_goals try linarith