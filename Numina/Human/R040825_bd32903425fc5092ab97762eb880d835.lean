import Mathlib

/-Given positive integers x, y, z satisfy the condition xyz = (14-x)(14-y)(14-z)
and x + y + z < 28, then the maximum value of x ^ 2 + y ^ 2 + z ^ 2 is 219 -/
theorem algebra_294006 (x y z : ℤ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y * z = (14 - x) * (14 - y) * (14 - z)) (h1 : x + y + z < 28) :
    x ^ 2 + y ^ 2 + z ^ 2 ≤ 219 := by 
  -- we show that x must be less than or equal to 13 --
  have h2 : x ≤ 13 := by
    by_contra h2
    push_neg at h2
    have h3 : (14 - x) ≤ 0 := by omega 
   -- now y + z must be less than 14, hence the following is negative, with h we get a contradiction --
    have h4 : (14 - x) * (14 - y) * (14 - z) ≤ 0 := by 
      have o: y + z < 14 := by  -- then we must have y + z < 14 --
        by_contra! no
        have contra: x + y + z ≥ 14 := by
          nlinarith
        omega
      have oy: y < 14 := by nlinarith
      have oz: z < 14 := by nlinarith
      replace oy: 14 - y ≥ 0 := by nlinarith
      replace oz: 14 - z ≥ 0 := by nlinarith
      have oyz: (14 - y) * (14 - z) ≥ 0 := by
        nlinarith [oy, oz]
      rw [show (14 - x) * (14 - y) * (14 - z) = (14 - x) * ((14 - y) * (14 - z)) by ring]
      nlinarith [h3, oyz]
    rw [← h] at h4
    have contra: 0 < x * y * z := by
      have lyz: y * z > 0 := by
        nlinarith [hy, hz]
      rw [show x * y * z = x * (y * z) by ring]
      nlinarith [hx, lyz]
    omega
  -- similarly, we show that y must be less than or equal to 13 --
  have h3 : y ≤ 13 := by
    by_contra h2
    push_neg at h2
    have h3 : (14 - y) ≤ 0 := by omega 
   -- now y + z must be less than 14, hence the following is negative, with h we get a contradiction --
    have h4 : (14 - x) * (14 - y) * (14 - z) ≤ 0 := by 
      have o: x + z < 14 := by  -- then we must have y + z < 14 --
        by_contra! no
        have contra: x + y + z ≥ 14 := by
          nlinarith
        omega
      have ox: x < 14 := by nlinarith
      have oz: z < 14 := by nlinarith
      replace ox: 14 - x ≥ 0 := by nlinarith
      replace oz: 14 - z ≥ 0 := by nlinarith
      have oxz: (14 - x) * (14 - z) ≥ 0 := by
        nlinarith [ox, oz]
      rw [show (14 - x) * (14 - y) * (14 - z) = (14 - y) * ((14 - x) * (14 - z)) by ring]
      nlinarith [h3, oxz]
    rw [← h] at h4
    have contra: 0 < x * y * z := by
      have lyz: y * z > 0 := by
        nlinarith [hy, hz]
      rw [show x * y * z = x * (y * z) by ring]
      nlinarith [hx, lyz]
    omega
  have h4 : z ≤ 13 := by
    by_contra h2
    push_neg at h2
    have h3 : (14 - z) ≤ 0 := by omega 
   -- now y + z must be less than 14, hence the following is negative, with h we get a contradiction --
    have h4 : (14 - x) * (14 - y) * (14 - z) ≤ 0 := by 
      have o: x + y < 14 := by  -- then we must have y + z < 14 --
        by_contra! no
        have contra: x + y + z ≥ 14 := by
          nlinarith
        omega
      have ox: x < 14 := by nlinarith
      have oy: y < 14 := by nlinarith
      replace ox: 14 - x ≥ 0 := by nlinarith
      replace oy: 14 - y ≥ 0 := by nlinarith
      have oxy: (14 - x) * (14 - y) ≥ 0 := by
        nlinarith [ox, oy]
      rw [show (14 - x) * (14 - y) * (14 - z) = (14 - z) * ((14 - x) * (14 - y)) by ring]
      nlinarith [h3, oxy]
    rw [← h] at h4
    have contra: 0 < x * y * z := by
      have lyz: y * z > 0 := by
        nlinarith [hy, hz]
      rw [show x * y * z = x * (y * z) by ring]
      nlinarith [hx, lyz]
    omega

  -- now we have x, y and z are less than or equal to 13, so there are only finite cases, we can check them all --
  interval_cases x <;> interval_cases y <;> interval_cases z <;> omega