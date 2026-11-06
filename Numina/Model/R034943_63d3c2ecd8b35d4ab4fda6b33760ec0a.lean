import Mathlib

theorem algebra_211856 {a : ℝ} (ha : a ≠ 1) (f g : ℝ → ℝ)
    (hf : f = fun x => (3 * x - 11) / (x - 3)) (hg : g = fun x => (12 * x - a) / (4 * x - 1))
    (hfg : ∀ x, g x = f (-x + 3)) :
    a = -5 ∨ a = 11 := by
  have eq1 := hfg 0
  simp [hf, hg] at eq1
  have eq2 := hfg 1
  norm_num [hf, hg] at eq2
  have eq3 := hfg 3
  norm_num [hf, hg] at eq3
  have eq4 := hfg (5 / 4)
  norm_num [hf, hg] at eq4
  have eq5 : a = (0 : ℝ) := by 
    linarith
  have eq8 : a = (-3 : ℝ) := by 
    linarith
  linarith