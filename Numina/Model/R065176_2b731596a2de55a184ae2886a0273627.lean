import Mathlib

theorem algebra_232599 {x y : ℕ} (h1 : x * (y + 5) = x * y + 1250) (h2 : (x + 7) * y = x * y + 3150) :
    x + y = 700 := by
  -- From equation 1: x * (y + 5) = x * y + 1250. Expanding left side: x*y + 5x = x*y + 1250
  -- Subtract x*y from both sides: 5x = 1250
  have eq1 : 5 * x = 1250 := by
    linarith [h1]
  -- Solving 5x = 1250 gives x = 250
  have hx : x = 250 := by
    omega
  -- From equation 2: (x + 7) * y = x * y + 3150. Expanding left side: x*y + 7y = x*y + 3150
  -- Subtract x*y from both sides: 7y = 3150
  have eq2 : 7 * y = 3150 := by
    linarith [h2]
  -- Solving 7y = 3150 gives y = 450
  have hy : y = 450 := by
    omega
  -- Now that we have x = 250 and y = 450, so x + y = 700
  calc
    x + y = 250 + 450 := by rw [hx, hy]
    _ = 700 := by norm_num