import Mathlib

theorem algebra_167600 {f g : ℝ → ℝ}
    (hfg : ∀ x, f (x + 4) + 2 * g (2 * x + 7) = (x + 3) / 2 ∧ f ((x + 3) / 2) + g (x + 2) = x + 6) :
    ∀ x, f x = (7 / 2) * x + (13 / 2) := by
  have eq1 : ∀ (y : ℝ), g y = y + 4 - f ((y + 1) / 2) := by
    intro y
    have eq2 := (hfg (y - 2)).2
    simp at eq2 ⊢
    ring_nf at eq2 ⊢
    linarith
  have eq5 : ∀ (x : ℝ), f (x + 4) = (7 / 2) * x + 41 / 2 := by
    intro x
    have eq1a : f (x + 4) + 2 * g (2 * x + 7) = (x + 3) / 2 := (hfg x).1
    have eq1b : f ((x + 3) / 2) + g (x + 2) = x + 6 := (hfg x).2 
    have eq3 : g (2 * x + 7) = ( (2 * x + 7 : ℝ) + 4 ) - f (( (2 * x + 7 + 1) / 2 ) ) := by
      apply eq1
    have eq4 : ( (2 * x + 7 + 1) / 2 ) = x + 4 := by 
      ring_nf 
    rw [eq4] at eq3
    rw [eq3] at eq1a
    linarith
  intro x
  have eq7 : f x = (7 / 2) * x + (13 / 2) := by
    have eq8 := eq5 (x - 4)
    rw [show x - 4 + 4 = (x : ℝ) by ring] at eq8
    linarith 
  exact_mod_cast eq7