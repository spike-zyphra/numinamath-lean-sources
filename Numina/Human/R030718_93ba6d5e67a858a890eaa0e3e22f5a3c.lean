import Mathlib

theorem algebra_177259 {V W : ℕ} (hV : V ∈ Finset.Icc 10 99) (hW : W ∈ Finset.Icc 10 99) (hlt : W ≤ V)
    (quot : (1000 * V + W) / (1000 * W + 10 * V) = 2)
    (rmd : (1000 * V + W) % (1000 * W + 10 * V) = 590) (h : 2 * V + 3 * W = 72) :
    V = 21 ∧ W = 10 := by
-- Unfold the boundary conditions for $V$ and $W$
  simp at hV hW
  rcases hV with ⟨hVl, hVu⟩
  rcases hW with ⟨hWl, hWu⟩
-- Rewrite the quotient and remainder conditions to one equation via `Nat.div_add_mod`
  have := Nat.div_add_mod (1000 * V + W) (1000 * W + 10 * V)
  rw [quot, rmd] at this; ring_nf at this
-- Disjunct the goal via `constructor`
  constructor
-- Since the problem now becomes solving two linear equations of natural numbers, we can use `omega` tactics to finish 
  all_goals omega