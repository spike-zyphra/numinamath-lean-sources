import Mathlib

theorem algebra_247361 (total_population : ℝ) (h : total_population ≠ 0)
    (mortality_rate : ℝ) (hm : mortality_rate = 15 / 100 * total_population * 8 / 100) :
    mortality_rate / total_population = 1.2 / 100 := by 
  have h1 : mortality_rate = 0.012 * total_population := by 
    rw [hm]
    ring_nf
  calc 
    mortality_rate / total_population = (0.012 * total_population) / total_population := by rw [h1]
    _ = 0.012 := by 
      field_simp [h]
      all_goals linarith
    _ = 1.2 / 100 := by norm_num