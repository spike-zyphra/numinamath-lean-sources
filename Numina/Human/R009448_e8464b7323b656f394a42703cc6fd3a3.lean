import Mathlib
open Real

/- Given that
\[2^{-\frac{3}{2} + 2 \cos \theta} + 1 = 2^{\frac{1}{4} + \cos \theta},\]compute $\cos 2 \theta.$ -/
theorem calculus_15258 (θ : ℝ) (hθ : (2 : ℝ)^(-3/2 + 2 * cos θ) + 1 = (2 : ℝ)^(1/4 + cos θ)) :
    cos (2 * θ) = 1/8 := by
  -- Simplify the equation
  rw [rpow_add (by norm_num), rpow_add (by norm_num)] at hθ
  rw [show 2 * cos θ = cos θ * (2 : ℕ) by ring] at hθ
  rw [rpow_mul_natCast (by norm_num)] at hθ
  -- Rewrite the equation in terms of x := 2^cos θ
  let x := (2 : ℝ) ^ cos θ
  change 2 ^ (-3 / 2) * x ^ 2 + 1 = 2 ^ (1 / 4) * x at hθ
  -- Some simple algebraic manipulations
  have h1 : (2 : ℝ) ^ (-3 / 2 : ℝ) = (2 ^ (-3 / 4 : ℝ)) ^ 2 := by
    rw [← rpow_two, ← rpow_mul (by norm_num)]
    norm_num
  have h2 : (2 : ℝ) ^ (1 / 4 : ℝ) = (2 ^ (-3 / 4 : ℝ)) * 2 := by
    nth_rw 3 [← rpow_one 2]
    rw [← rpow_add (by norm_num)]
    norm_num
  rw [h1, h2, ← sub_eq_zero] at hθ
  clear h1 h2
  -- We find the LHS of hθ is a perfect square
  rw [show ((2 : ℝ) ^ (-3 / 4 : ℝ)) ^ 2 * x ^ 2 + 1 - 2 ^ (-3 / 4 : ℝ) * 2 * x = (2 ^ (-3 / 4 : ℝ) * x - 1) ^ 2 by ring] at hθ
  -- Thus we have x = 2^(3/4)
  apply pow_eq_zero at hθ
  rw [sub_eq_zero] at hθ
  replace hθ : x = ((2 : ℝ) ^ (-3 / 4 : ℝ))⁻¹ := (DivisionMonoid.inv_eq_of_mul _ _ hθ).symm
  rw [← rpow_neg (by norm_num)] at hθ
  norm_num at hθ
  -- And we get cos θ = 3/4
  apply_fun logb 2 at hθ
  simp [x] at hθ
  -- Finally, we compute cos 2θ by double angle formula
  rw [cos_two_mul, hθ]
  norm_num
