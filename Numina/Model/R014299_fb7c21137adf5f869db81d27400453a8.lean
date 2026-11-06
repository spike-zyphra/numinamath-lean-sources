import Mathlib

theorem algebra_9699 (x : ℂ) (hx : x ^ 4 + x ^ 3 + x ^ 2 + x + 1 = 0) :
    x ^ 2023 + x ^ 422 + x ^ 1234 + x ^ 4321 = -1 := by

  have h1 : x ≠ 0 := by
    by_contra h
    rw [h] at hx
    norm_num at hx
  
  have h2 : x ^ 5 = 1 := by 
    have eq1 : x ^ 4 + x ^ 3 + x ^ 2 + x + 1 = 0 := hx
    have eq2 : (x - 1) * (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) = 0 := by
      rw [eq1]
      norm_num

    have eq3 : (x - 1) * (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) = x ^ 5 - 1 := by
      ring

    rw [eq3] at eq2
    have h3 : x ^ 5 - 1 = 0 := by
      simpa using eq2

    have h4 : x ^ 5 = 1 := by
      calc
        x ^ 5 = (x ^ 5 - 1) + 1 := by ring
        _ = (0) + 1 := by rw [h3]
        _ = 1 := by ring
    exact h4
  
  have hx2023 : x ^ 2023 = x ^ 3 := by
    calc
      x ^ 2023 = x ^ (5 * 404 + 3) := by norm_num
      _ = (x ^ 5) ^ 404 * x ^ 3 := by ring
      _ = (1) ^ 404 * x ^ 3 := by rw [h2]
      _ = x ^ 3 := by ring

  have hx422 : x ^ 422 = x ^ 2 := by
    calc
      x ^ 422 = x ^ (5 * 84 + 2) := by norm_num
      _ = (x ^ 5) ^ 84 * x ^ 2 := by ring
      _ = (1) ^ 84 * x ^ 2 := by rw [h2]
      _ = x ^ 2 := by ring
  
  have hx1234 : x ^ 1234 = x ^ 4 := by 
    calc 
      x ^ 1234 = x ^ (5 * 246 + 4) := by norm_num 
      _ = (x ^ 5) ^ 246 * x ^ 4 := by ring 
      _ = (1) ^ 246 * x ^ 4 := by rw [h2] 
      _ = x ^ 4 := by ring 
  

  have hx4321 : x ^ 4321 = x := by 
    calc 
      x ^ 4321 = x ^ (5 * 864 + 1) := by norm_num 
      _ = (x ^ 5) ^ 864 * x := by ring 
      _ = (1) ^ 864 * x := by rw [h2] 
      _ = x := by ring 
  

  rw [hx2023, hx422, hx1234, hx4321]
  
  have eq1 : x ^ 4 + x ^ 3 + x ^ 2 + x + 1 = 0 := hx
  have eq2 : x ^ 4 + x ^ 3 + x ^ 2 + x = -1 := by 
    calc
      x ^ 4 + x ^ 3 + x ^ 2 + x = (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) - 1 := by ring
      _ = (0) - 1 := by rw [hx]
      _ = -1 := by ring 
  calc
    x ^ 3 + x ^ 2 + x ^ 4 + x = x ^ 4 + x ^ 3 + x ^ 2 + x := by ring 
    _ = -1 := by exact_mod_cast eq2