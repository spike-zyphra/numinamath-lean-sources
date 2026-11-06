import Mathlib

theorem algebra_299625 {f : ℝ → ℝ} (hf : ∀ x, x ≠ 1 → f x + 2 * f ((x + 2002) / (x - 1)) = 4015 - x) :
    f 2004 = 2005 := by
  have eq1 := hf 2004 (by norm_num)
  have eq1_simp : (2004 + 2002 : ℝ) / (2004 - 1) = (2 : ℝ) := by norm_num
  rw [eq1_simp] at eq1

  have eq2 := hf 2 (by norm_num)
  have eq2_simp : (2 + 2002 : ℝ) / (2 - 1) = (2004 : ℝ) := by norm_num
  rw [eq2_simp] at eq2
  
  norm_num at eq1 eq2

  linarith [eq1, eq2]