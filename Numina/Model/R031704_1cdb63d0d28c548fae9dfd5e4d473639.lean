import Mathlib

theorem algebra_95585 (A B C normal_minute metric_minute : ℕ) (normal_time metric_time : ℕ × ℕ) (hnormal : normal_minute = 60*normal_time.1 + normal_time.2) (hmetric : metric_minute = 100*metric_time.1 + metric_time.2) (hratio : metric_minute/normal_minute = (10*100 : ℚ)/(24*60)) (h_normal_time : normal_time = ⟨6,36⟩) (h_metric_time : metric_time = ⟨A,10*B+C⟩) : 100 * A + 10 * B + C = 275 := by 
  have h1 : normal_minute = 396 := by 
    rw [h_normal_time] at hnormal
    norm_num at hnormal ⊢ 
    omega 
  have h2 : (metric_minute : ℚ) / (396 : ℚ) = (1000 : ℚ) / (1440 : ℚ) := by
    rw [show (normal_minute : ℚ) = (396 : ℚ) by exact_mod_cast h1] at hratio 
    norm_num [show (10 * 100 : ℚ) = (1000 : ℚ) by norm_num, 
      show (24 * 60 : ℚ) = (1440 : ℚ) by norm_num] at hratio ⊢ 
    linarith
  have h3 : (metric_minute : ℚ) = 275 := by 
    have h4 : (metric_minute : ℚ) / (396 : ℚ) = (1000 : ℚ) / (1440 : ℚ) := h2 
    field_simp at h4 ⊢
    linarith 
  have h4 : metric_minute = 275 := by 
    exact_mod_cast h3 
  rw [h_metric_time] at hmetric 
  rw [h4] at hmetric 
  simp [Prod.fst, Prod.snd] at hmetric ⊢ 
  omega