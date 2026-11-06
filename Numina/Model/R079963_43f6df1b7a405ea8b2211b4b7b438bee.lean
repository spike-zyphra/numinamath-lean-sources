import Mathlib

theorem algebra_305272 {m n : ℤ} (hmn : m ≠ n) (h1 : m^2 = n + 2) (h2 : n^2 = m + 2) :
    m^3 - 2 * m * n + n^3 = -2 := by
  have h3 : (m - n) * (m + n + 1) = 0 := by 
    nlinarith
  have h5 : m - n ≠ 0 := by
    intro h
    apply hmn
    omega
  have h6 : m + n + 1 = 0 := by
    apply_fun (fun x : ℤ => x / (m - n)) at h3
    field_simp [h5] at h3
    linarith
  have h4 : m + n = -1 := by linarith
  have h7 : n = -1 - m := by linarith
  rw [h7]
  nlinarith [sq_pos_of_ne_zero (sub_ne_zero_of_ne hmn), sq_pos_of_ne_zero (sub_ne_zero_of_ne hmn.symm)]