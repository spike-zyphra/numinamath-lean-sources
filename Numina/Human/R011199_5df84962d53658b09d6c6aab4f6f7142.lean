import Mathlib
open Real

/- 15^30/45^15=
(A)(1/3)^15 (B)(1/3)^2 (C)1 (D)3^15 (E)5^15 -/

theorem algebra_97758 : (15:ℝ)^30 / 45^15 = 5^15 := by
  -- solve by converting these to the same bases and term elimination
  calc  (15:ℝ)^30 / 45^15
      = 15^30 / (15*3)^15               := by norm_num
    _ = 15^30 / ((15^15)*(3^15))        := by rw [mul_pow]
    _ = 15^30 / 15^15 / 3^15            := by rw [← div_div]
    _ = 15^((↑(30:ℕ):ℤ)-(↑15:ℕ)) / 3^15 := by rw [zpow_natCast_sub_natCast₀ (by simp)]
    _ = 15^15 / 3^15                    := by norm_num
    _ = (15/3)^15                       := by rw [← div_pow]
    _ = 5^15                            := by norm_num