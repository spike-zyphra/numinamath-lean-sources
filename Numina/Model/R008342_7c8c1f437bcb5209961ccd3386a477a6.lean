import Mathlib

theorem algebra_109804 {n m : ℕ} (hn : n > 0) (hm : m > 0)
    (h1 : n = 6 * (m + 1)) (h2 : n = 9 * (m - 1)) :
    n = 36 := by 
  have eq1 : 6 * (m + 1) = 9 * (m - 1) := by
    linarith [h1, h2]

  have hm5 : m = 5 := by 
    omega
  
  have hn36 : n = 36 := by 
    rw [hm5] at h1
    omega
  
  exact hn36