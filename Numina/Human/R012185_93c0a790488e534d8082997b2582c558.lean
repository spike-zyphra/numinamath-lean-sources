import Mathlib

theorem algebra_192689 {x y z t : ℤ} (h1 : x * z - 2 * y * t = 3)
  (h2 : x * t + y * z = 1) : (x, y, z, t) = (1, 0, 3, 1)
  ∨ (x, y, z, t) = (-1, 0, -3, -1) ∨ (x, y, z, t) = (3, 1, 1, 0)
  ∨ (x, y, z, t) = (-3, -1, -1, 0):= by 
  -- simpify the equations and find that (x ^ 2 + 2 * y ^ 2) * (z ^ 2 + 2 * t ^ 2) = 11
  have eq_aux : (x ^ 2 + 2 * y ^ 2) * (z ^ 2 + 2 * t ^ 2) = 11 := by
    calc
      _ = (x * z - 2 * y * t) ^ 2 + 2 * (x * t + y * z) ^ 2 := by ring
      _ = 11 := by rw [h1, h2]; norm_num
  -- by the equation above we can get these two cases 
  have eq_or : x ^ 2 + 2 * y ^ 2 = 1 ∨ z ^ 2 + 2 * t ^ 2 = 1 := by 
    have dvd_aux : 11 ∣ x ^ 2 + 2 * y ^ 2  ∨ 11 ∣ z ^ 2 + 2 * t ^ 2 := by 
      have aux : 11 ∣ (x ^ 2 + 2 * y ^ 2) * (z ^ 2 + 2 * t ^ 2)  := by 
        rw [eq_aux]
      refine Prime.dvd_or_dvd ?_ aux
      norm_num
    have pos1 : (x ^ 2 + 2 * y ^ 2) ≥ 1 := by 
      have aux :(x ^ 2 + 2 * y ^ 2) ≥ 0 := by positivity
      apply lt_of_le_of_ne aux
      by_contra hc
      rw [←hc] at eq_aux
      norm_num at eq_aux
    have pos2 : (z ^ 2 + 2 * t ^ 2) ≥ 1 := by 
      have aux :(z ^ 2 + 2 * t ^ 2) ≥ 0 := by positivity
      apply lt_of_le_of_ne aux
      by_contra hc
      rw [←hc] at eq_aux
      norm_num at eq_aux
    have le1 : (x ^ 2 + 2 * y ^ 2) ≤ 11 := by 
      rw [←eq_aux]
      nlinarith
    have le2 : (z ^ 2 + 2 * t ^ 2) ≤ 11 := by
      rw [←eq_aux]
      nlinarith
    obtain heq1 | heq2 := dvd_aux
    have ge1 : (x ^ 2 + 2 * y ^ 2) ≥  11 := by 
      exact Int.le_of_dvd pos1 heq1
    have eq1 : (x ^ 2 + 2 * y ^ 2) = 11 := by nlinarith
    rw [eq1] at eq_aux
    right
    omega
    have ge2 : (z ^ 2 + 2 * t ^ 2) ≥ 11 := by
      exact Int.le_of_dvd pos2 heq2
    have eq2 : (z ^ 2 + 2 * t ^ 2) = 11 := by nlinarith
    rw [eq2] at eq_aux
    left
    omega
  obtain h | h := eq_or
  have y_eq_zero : y = 0 := by nlinarith
  have xeq : x ^ 2 = 1 := by nlinarith
  have xeq_or : x = 1 ∨ x = - 1 := by 
    exact sq_eq_one_iff.mp xeq
  obtain hxeq | hxeq := xeq_or
  left
  simp
  have h' : (z ^ 2 + 2 * t ^ 2) = 11 := by 
    rw [h] at eq_aux
    omega
  rw [y_eq_zero, hxeq] at h2
  rw [y_eq_zero, hxeq] at h1
  simp_all
  right; left
  rw [y_eq_zero, hxeq] at h2
  rw [y_eq_zero, hxeq] at h1
  simp_all
  omega
  have t_eq_zero : t = 0 := by nlinarith
  have zeq : z ^ 2 = 1 := by nlinarith
  have zeq_or : z = 1 ∨ z = - 1 := by
    exact sq_eq_one_iff.mp zeq
  obtain hzeq | hzeq := zeq_or
  right; right; left
  simp_all
  right; right; right
  simp_all
  omega
