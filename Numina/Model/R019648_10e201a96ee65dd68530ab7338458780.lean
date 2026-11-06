import Mathlib

open Real

theorem algebra_12876 {f : ℝ → ℝ} (hf : f = fun x => 1 / (2 ^ x - 1) + 1 / 2) :
    Odd f := by 
  use (fun x => (1 / (2 ^ x - 1) - 1 / 2) / 2)
  funext x
  rw [hf]
  simp 
  <;> ring