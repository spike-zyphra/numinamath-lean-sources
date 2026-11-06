import Mathlib
open Real

theorem calculus_15258 (θ : ℝ) (hθ : (2 : ℝ)^(-3/2 + 2 * cos θ) + 1 = (2 : ℝ)^(1/4 + cos θ)) :
    cos (2 * θ) = 1/8 := by
  rw [rpow_add (by norm_num), rpow_add (by norm_num)] at hθ
  rw [show 2 * cos θ = cos θ * (2 : ℕ) by ring] at hθ
  rw [rpow_mul_natCast (by norm_num)] at hθ
  let x := (2 : ℝ) ^ cos θ
  change 2 ^ (-3 / 2) * x ^ 2 + 1 = 2 ^ (1 / 4) * x at hθ
  have h1 : (2 : ℝ) ^ (-3 / 2 : ℝ) = (2 ^ (-3 / 4 : ℝ)) ^ 2 := by
    rw [← rpow_two, ← rpow_mul (by norm_num)]
    norm_num
  have h2 : (2 : ℝ) ^ (1 / 4 : ℝ) = (2 ^ (-3 / 4 : ℝ)) * 2 := by
    nth_rw 3 [← rpow_one 2]
    rw [← rpow_add (by norm_num)]
    norm_num
  rw [h1, h2, ← sub_eq_zero] at hθ
  clear h1 h2
  rw [show ((2 : ℝ) ^ (-3 / 4 : ℝ)) ^ 2 * x ^ 2 + 1 - 2 ^ (-3 / 4 : ℝ) * 2 * x = (2 ^ (-3 / 4 : ℝ) * x - 1) ^ 2 by ring] at hθ
  apply pow_eq_zero at hθ
  rw [sub_eq_zero] at hθ
  replace hθ : x = ((2 : ℝ) ^ (-3 / 4 : ℝ))⁻¹ := (DivisionMonoid.inv_eq_of_mul _ _ hθ).symm
  rw [← rpow_neg (by norm_num)] at hθ
  have hcos : cos θ = 3 / 4 := by
    have h4 : (2 : ℝ) ^ cos θ = (2 : ℝ) ^ (3 / 4 : ℝ) := by
      rw [show (2 : ℝ) ^ cos θ = x by simp [x]]
      linarith [hθ]
    have h5 : cos θ = (3 / 4 : ℝ) := by
      apply_fun (Real.logb (2 : ℝ)) at h4
      simp at h4 ⊢
      linarith
    linarith
  have hcos2 : cos (2 * θ) = 2 * cos θ ^ 2 - 1 := by
    rw [cos_two_mul]
  rw [hcos2, hcos]
  norm_num