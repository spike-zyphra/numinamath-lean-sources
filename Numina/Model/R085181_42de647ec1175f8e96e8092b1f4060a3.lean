import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_126856 {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x)
  (h : ∃ m, f = λ x => (m - 1) * x^2 + 2 * m * x + 3) :
  StrictMonoOn f (Set.Ioo (-5) (-2)) := by
  rcases h with ⟨m, rfl⟩
  have h1 := hf 1
  simp at h1
  have hm : m = 0 := by linarith
  intro x hx y hy hxy
  have hx1 : -5 < x := hx.1
  have hx2 : x < -2 := hx.2
  have hy1 : -5 < y := hy.1
  have hy2 : y < -2 := hy.2
  have hx_neg : x < 0 := by linarith
  have hy_neg : y < 0 := by linarith
  have h3 : (m - 1) * x^2 + 2 * m * x + 3 = -x ^ 2 + 3 := by
    rw [show m = 0 by linarith]
    all_goals
      try ring
      try simp
      try linarith
      try tauto
  have h4 : (m - 1) * y^2 + 2 * m * y + 3 = -y ^ 2 + 3 := by
    rw [show m = 0 by linarith]
    all_goals
      try ring
      try simp
      try linarith
      try tauto
  simp [h3, h4]
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x + y), show x < y from by linarith, show x < (y) from by linarith, show x < 0 from by linarith, show y < 0 from by linarith, show x * x > 0 from by nlinarith, show y * y > 0 from by nlinarith, show x * y > 0 from by nlinarith, show x ^ 2 > y ^ 2 from by nlinarith]