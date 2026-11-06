import Mathlib

theorem algebra_13974 {f g h : ℝ → ℝ} (hf : f = fun x => 3 * x + 4) (hg : g = fun x => 2 * x - 3)
    (hh : h = fun x => f (g x)) :
    Function.invFun h = fun x => (x + 5) / 6 := by
  have h_def : h = fun x => 6 * x - 5 := by
    rw [hh, hg, hf]
    funext x
    simp
    ring
  rw [h_def]
  funext y
  have : ∀ x : ℝ, (6 * x - 5) = y ↔ x = (y + 5) / 6 := by
    intro x
    constructor
    · -- Assume $6x - 5 = y$, prove $x = (y + 5) / 6$
      intro h_eq
      linarith
    · -- Assume $x = (y + 5) / 6$, prove $6x - 5 = y$
      intro h_eq
      linarith
  simp_all [Function.invFun]