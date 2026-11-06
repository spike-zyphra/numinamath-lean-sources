import Mathlib

theorem algebra_167302 (xiao_ming xiao_hua xiao_gang : ℕ)
    (h1 : xiao_ming + xiao_hua + xiao_gang = 363)
    (h2 : xiao_ming * 6 = xiao_hua * 7)
    (h3 : xiao_gang * 5 = xiao_ming * 8) :
    xiao_ming = 105 ∧ xiao_hua = 90 ∧ xiao_gang = 168 := by
  have h4 : xiao_ming = 105 := by 
    omega
  have h5 : xiao_hua = 90 := by
    rw [h4] at h2
    omega
  have h6 : xiao_gang = 168 := by 
    rw [h4] at h3
    omega
  exact ⟨h4, h5, h6⟩