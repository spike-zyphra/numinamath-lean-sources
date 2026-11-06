import Mathlib

/- [Periodicity and Aperiodicity] The function $f(x)$ is defined for all real numbers, and for any $x$, the equalities $f(x+2) = f(2-x)$ and $f(x+7) = f(7-x)$ hold.

Prove that $f(x)$ is a periodic function. -/
theorem algebra_242806 {f : ℝ → ℝ} (h : ∀ x, f (x + 2) = f (2 - x)) (h' : ∀ x, f (x + 7) = f (7 - x)) :
    ∃ c, Function.Periodic f c := by
  -- show that c = 10 works
  use 10
  dsimp [Function.Periodic]
  -- we need to prove that f (x + 10) = f x for all x:
  -- f (x + 10) = f ((x + 3) + 7)
  --            = f (4 - x)        (from h')
  --            = f ((2 - x) + 2)
  --            = f x              (from h)
  intro x
  calc
    f (x + 10) = f ((x + 3) + 7) := by rw [add_assoc]; norm_num
    _ = f (4 - x) := by rw [h']; congr 1; ring
    _ = f ((2 - x) + 2) := by congr 1; ring
    _ = f x := by rw [h]; congr 1; ring