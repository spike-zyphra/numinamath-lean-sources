import Mathlib

theorem algebra_283183 {N : ℕ} (hN : N > 0) (h : 12000 * (1 + 6 / 100) ^ (30 * N) = 12000 * (1 + 1 / 100) ^ (30 * N) + 12000 * (1 + 2 / 100) ^ (30 * N)) :
    N ≤ 59 := by 
  have h1 : (1 + 6 / 100 : ℕ) = 1 := by 
    norm_num 
  have h2 : (1 + 1 / 100 : ℕ) = 1 := by 
    norm_num 
  have h3 : (1 + 2 / 100 : ℕ) = 1 := by 
    norm_num 
  simp [h1, h2, h3] at h 
  all_goals omega