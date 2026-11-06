import Mathlib

theorem algebra_13112 {a : Fin 12 → ℝ} {highest lowest : ℝ}
    (h_highest : IsGreatest (a '' univ) highest)
    (h_lowest : IsLeast (a '' univ) lowest)
    (h1 : (∑ i, a i) / 12 = 82)
    (h2 : (∑ i, a i - highest - lowest) / (12 - 2) = 84)
    (h3 : highest = 98) :
    lowest = 46 := by
  have h4 : ∑ i : Fin 12, a i = 984 := by 
    have h_sum : (∑ i : Fin 12, a i) / 12 = 82 := h1
    calc (∑ i : Fin 12, a i) = (∑ i : Fin 12, a i) / 12 * 12 := by ring
      _ = 82 * 12 := by rw [h_sum]
      _ = 984 := by norm_num
  
  have h5 : ∑ i : Fin 12, a i - highest - lowest = 840 := by
    have h_new_sum : (∑ i : Fin 12, a i - highest - lowest) / (12 - 2) = 84 := h2
    calc (∑ i : Fin 12, a i - highest - lowest) = (∑ i : Fin 12, a i - highest - lowest) / (12 - 2) * (12 - 2) := by ring_nf
      _ = 84 * (12 - 2) := by rw [h2]
      _ = 840 := by norm_num
  
  rw [show ∑ i : Fin 12, a i = 984 by rw [h4]] at h5
  rw [show highest = 98 by rw [h3]] at h5
  linarith