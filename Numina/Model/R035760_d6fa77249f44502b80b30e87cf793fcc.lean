import Mathlib

theorem algebra_197289 {f g : ℝ → ℝ} (hf : ∀ x, x ≠ -1 → x ≠ 0 → x ≠ 1 → x * f x - 1 / x * g (1 / x) = 1)
    (hg : ∀ x, x ≠ -1 → x ≠ 0 → x ≠ 1 → (1 / x ^ 2) * f x = (x ^ 2) * g x) :
    ∀ x, x ≠ -1 → x ≠ 0 → x ≠ 1 → f x = 1 / (x - x ^ 3) ∧ g x = -(x) := by
  intro x hx1 hx2 hx3
  have eq1 := hf 2 (by norm_num) (by norm_num) (by norm_num)
  have eq2 := hg 2 (by norm_num) (by norm_num) (by norm_num)
  have eq3 := hf (1/2 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have eq4 := hg (1/2 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  norm_num at eq1 eq2 eq3 eq4
  all_goals
    linarith