import Mathlib

theorem algebra_174995 (x y z : ℕ) 
    (hx : 2000 = x * 20)  -- 第一工人组装x个，每个20 Ft
    (hy : y = 75)         -- 第二工人组装75个
    (hz : 1200 = z * 20)  -- 第三工人组装z个，每个20 Ft
    : x + y + z = 235 := by
  have hx' : x = 100 := by
    omega
  have hz' : z = 60 := by 
    omega
  calc
    x + y + z = 100 + 75 + 60 := by 
      rw [hx', hy, hz']
    _ = 235 := by 
      omega