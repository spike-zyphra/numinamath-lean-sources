import Mathlib

theorem algebra_86300 {a r : ℝ} (hr : r ≠ 0) (h5 : a * r^4 = Nat.factorial 5) (h6 : a * r^5 = Nat.factorial 6) :
    a * r^3 = 20 := by

  have h5' : a * r^4 = 120 := by
    norm_num [Nat.factorial] at h5 ⊢
    linarith

  have h6' : a * r^5 = 720 := by
    norm_num [Nat.factorial] at h6 ⊢
    linarith

  have hr_eq : r = 6 := by
    have h7 : a * r^5 = (a * r^4) * r := by ring
    rw [h7] at h6'
    rw [h5'] at h6'
    nlinarith

  have ha : a = 5 / 54 := by
    rw [hr_eq] at h5'
    nlinarith

  rw [ha, hr_eq]
  norm_num