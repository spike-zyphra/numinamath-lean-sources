import Mathlib

theorem calculus_119279 {f : ℝ → ℝ} (hf : ∀ x, f x = -x) :
    {x | f x = 0} = {x | deriv f x + x ^ 2 + 1 = 0} := by
  have f_eq : f = fun x => -x := by
    funext x
    exact hf x
  have deriv_f : ∀ x, deriv f x = -1 := by
    intro x
    rw [f_eq]
    simp
  ext x
  simp [Set.mem_setOf_eq, f_eq, deriv_f]
  <;> norm_num
  <;> tauto