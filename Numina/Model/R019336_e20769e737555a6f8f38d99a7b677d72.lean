import Mathlib

theorem algebra_4757 {f g h : ℝ → ℝ} (hf : f = fun x => x + 1)
    (hg : g = fun x => abs x) (hh : h = fun x => g (f x)) :
    h (Real.pi ^ 2) = Real.pi ^ 2 + 1 := by
  have h_eq : h = fun x => abs (x + 1) := by
    funext x
    rw [hh, hf, hg]
    all_goals simp
    <;> try tauto
  rw [h_eq]
  have h1 : Real.pi ^ 2 + 1 > 0 := by
    positivity
  simp [abs_of_pos, h1]
  <;> try tauto