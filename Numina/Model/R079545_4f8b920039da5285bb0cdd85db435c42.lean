import Mathlib

theorem algebra_73581 {n : ℕ} (hn : n > 0) (h1 : n + 50 = m) (h2 : m * 150 = p)
    (h3 : n + m + p = 1709) :
    IsGreatest {x | x.Prime ∧ x ∣ n} 17 := by 
  have h4 : m = n + 50 := by 
    omega 
  rw [h4] at h2 h3 
  -- Now h2 is (n + 50) * 150 = p
  -- And h3 is n + (n + 50) + p = 1709
  -- Let's substitute p from h2 into h3:
  -- p = (n + 50) * 150
  omega