import Mathlib

theorem algebra_293990 (f : ℝ → ℝ) (h : ∀ a b, f (a + b) + f (a - b) = 2 * f a * f b)
    (hc : ∃ c, 0 < c ∧ f (c / 2) = 0) :
    ∃ c, 0 < c ∧ Function.Periodic f (2 * c) := by 
  rcases hc with ⟨c, hc_pos, hc0⟩
  use c
  constructor
  · -- Show c > 0
    exact hc_pos
  · -- Show f is periodic with period 2 * c
    unfold Function.Periodic
    intro x
    have h1 : ∀ x : ℝ, f (x + c) = - f x := by
      intro x
      have eq1 : f (x + c) + f x = 2 * f (x + c / 2) * f (c / 2) := by
        specialize h (x + c / 2) (c / 2)
        have eq2 : (x + c / 2 : ℝ) + (c / 2 : ℝ) = (x + c : ℝ) := by ring
        have eq3 : (x + c / 2 : ℝ) - (c / 2 : ℝ) = (x : ℝ) := by ring
        rw [eq2, eq3] at h
        linarith
      rw [hc0] at eq1
      linarith
    calc
      f (x + 2 * c) = f ((x + c) + c) := by ring_nf
      _ = -f (x + c) := by rw [h1 (x + c)]
      _ = -(-f x) := by rw [h1 x]
      _ = f x := by ring