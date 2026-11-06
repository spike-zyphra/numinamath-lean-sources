import Mathlib

theorem algebra_123150 {f g : ℝ → ℝ} (a b c : ℝ)
    (hfg : ∀ x y, f x * g y = a * x * y + b * x + c * y + 1) : a = b * c := by
  have eq1 := hfg 0 0
  have eq2 := hfg 0 1
  have eq3 := hfg 1 0
  have eq4 := hfg 1 1
  -- Simplify equations
  have eq5 : f 0 * g 0 = 1 := by
    linarith
  have eq6 : f 0 * g 1 = c + 1 := by
    linarith
  have eq7 : f 1 * g 0 = b + 1 := by
    linarith
  have eq8 : f 1 * g 1 = a + b + c + 1 := by
    linarith
  -- Multiply eq6 and eq7
  have eq9 : (f 0 * g 1) * (f 1 * g 0) = (c + 1) * (b + 1) := by
    rw [eq6, eq7]
  -- Rearrange left side of eq9
  have eq10 : (f 0 * g 1) * (f 1 * g 0) = (f 0 * g 0) * (f 1 * g 1) := by
    ring
  rw [eq10] at eq9
  rw [eq5, eq8] at eq9
  -- Simplify equation to get desired equality
  linarith