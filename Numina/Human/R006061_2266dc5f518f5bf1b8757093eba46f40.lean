import Mathlib
open Real

/-
Find all real solutions to $x^{3}+(x+1)^{3}+(x+2)^{3}=(x+3)^{3}$.
-/
theorem algebra_611334 {x : ℝ} (h: x^3 + (x+1)^3 + (x+2)^3 = (x+3)^3): x=3 := by
  ring_nf at h

  -- Simpify the equation using `ring_nf` tactic which simplifies and expands polynomial expressions, bringing them to a normal form.
  have h': 2*x^3 - 12*x - 18 = 0 := by linarith
  have : 2*(x-3)*(x^2 + 3*x + 3) = 0 := by linarith

  -- Factorize the left hand side of the simplified equation as $2(x-3)(x^2+3x+3)=0$.
  have h'': (x-3)*(x^2 + 3*x + 3) = 0 := by linarith

  -- Extract one possible solution since the x^2 + 3*x + 3 > 0
  have hneq : x^2 + 3*x + 3 > 0 := by
    calc
      _ = (x + 3/2)^2 + 3/4 := by ring_nf
      _ ≥ 3/4 := by simp; apply sq_nonneg
      _ > 0 := by norm_num
  have h_xeqm3 : x - 3 = 0 := by
    calc
      _ = ((x-3)*(x^2 + 3*x + 3))/(x^2 + 3*x + 3) := by field_simp
      _ = 0/(x^2 + 3*x + 3) := by rw [h'']
      _ = 0 := by norm_num
  linarith



