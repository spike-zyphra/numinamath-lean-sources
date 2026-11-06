import Mathlib

theorem algebra_257328 {f : ℝ → ℝ} (hf : ∀ x, f (x + 2) - 2 = 2 ^ x) :
    f = fun x => 2 ^ (x - 2) + 2 := by 
  funext x
  have eq2 := hf (x - 2)
  have eq3 : f x - 2 = (2 : ℝ) ^ (x - 2) := by
    rw [show (x - 2 : ℝ) + 2 = x by ring] at eq2
    linarith
  linarith