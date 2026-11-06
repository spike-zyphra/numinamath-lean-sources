import Mathlib

theorem algebra_18725 {f g h : ℝ → ℝ}
    (hf : f = fun x => 7 * x + 5) (hg : g = fun x => x - 1)
    (hh : h = fun x => f (g x)) : h.invFun = fun (x : ℝ) ↦ (x + 2) / 7 := by
  have h_def : h = fun x => 7 * x - 2 := by
    rw [hh, hg, hf]
    funext x
    simp
    ring
  rw [h_def]
  funext y
  have : ∀ (x : ℝ), (7 * x - 2) = y ↔ x = (y + 2) / 7 := by
    intro x
    constructor
    · -- Assume 7 * x - 2 = y, prove x = (y + 2) / 7
      intro h_eq
      linarith
    · -- Assume x = (y + 2) / 7, prove 7 * x - 2 = y
      intro h_eq
      linarith
  simp_all [Function.invFun, this]
  <;> try { aesop }
  <;> try { linarith }