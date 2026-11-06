import Mathlib

theorem algebra_218332 (f : ℝ → ℝ) :
    ∃ g h, f = g + h ∧ Odd g ∧ Even h := by 
  use (fun x => (f x - f (-x)) / 2), (fun x => (f x + f (-x)) / 2)
  constructor 
  · -- Show f = g + h 
    funext x 
    simp 
    <;> ring 
  constructor 
  · -- Show g is odd 
    unfold Odd 
    use (fun x => ((f x - f (-x) - 2) / 4))
    funext x 
    simp 
    <;> ring 
  · -- Show h is even 
    unfold Even 
    use (fun x => (f x + f (-x)) / 4)
    funext x 
    simp 
    <;> ring