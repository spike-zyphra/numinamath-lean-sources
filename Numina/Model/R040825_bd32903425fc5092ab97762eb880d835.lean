import Mathlib

theorem algebra_294006 (x y z : ℤ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y * z = (14 - x) * (14 - y) * (14 - z)) (h1 : x + y + z < 28) :
    x ^ 2 + y ^ 2 + z ^ 2 ≤ 219 := by
  have h2 : x ≤ 13 := by
    by_contra h2
    push_neg at h2
    have h3 : (14 - x) ≤ 0 := by omega
    have h4 : (14 - x) * (14 - y) * (14 - z) ≤ 0 := by
      have o: y + z < 14 := by
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
  have h3 : y ≤ 13 := by
    by_contra h2
    push_neg at h2
    have h3 : (14 - y) ≤ 0 := by omega
    have h4 : (14 - x) * (14 - y) * (14 - z) ≤ 0 := by
      have o: x + z < 14 := by
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
    have h4 : (14 - x) * (14 - y) * (14 - z) ≤ 0 := by
      have o: x + y < 14 := by
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
  interval_cases x <;> interval_cases y <;> interval_cases z <;> omega