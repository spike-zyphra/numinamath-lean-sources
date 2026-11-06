import Mathlib

theorem algebra_213212 (o g c n h r : ℝ)
    (h₀ : o + g + c + n + h + r = 557.10)
    (h₁ : o = 174.20 - 137.62 - 151.42 - 23.98 - 38.16 - 31.71)
    (h₂ : g = 137.62 - 6.39 - 1.90)
    (h₃ : c = 151.42 - 9.20 - 3.27)
    (h₄ : n = 23.98 - 7.39 - 1.90)
    (h₅ : h = 38.16 - 2.56 - 1.89)
    (h₆ : r = 31.71 - 6.15 - 0.04) :
    o = 32.54 ∧ g = 2.21 ∧ r = 14.81 := by
  have h1' : o = -208.69 := by 
    rw [h₁]
    norm_num
  have h2' : g = 129.33 := by 
    rw [h₂]
    norm_num
  have h3' : c = 138.95 := by 
    rw [h₃]
    norm_num
  have h4' : n = 14.69 := by 
    rw [h₄]
    norm_num
  have h5' : h = 33.71 := by 
    rw [h₅]
    norm_num
  have h6' : r = 25.52 := by 
    rw [h₆]
    norm_num
  have h_sum : o + g + c + n + h + r = 133.51 := by 
    rw [h1', h2', h3', h4', h5', h6']
    norm_num
  have h_contra : (557.10 : ℝ) = 133.51 := by 
    linarith [h₀, h_sum]
  exfalso
  norm_num at h_contra