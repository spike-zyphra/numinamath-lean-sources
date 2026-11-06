import Mathlib

/- ## Task 12/90

Determine all triples $(x, y, z)$ of nonnegative integers $x, y$, and $z$ that satisfy the Diophantine equation $3 x+4 y+5 z=30$ and whose sum $s=x+y+z$ is a prime number, through logical reasoning (thus, a solution approach based on systematic trial and error is excluded!). -/
theorem number_theory_161491 (x y z : ℕ) (h₀ : 3 * x + 4 * y + 5 * z = 30) (h₁ : (x + y + z).Prime) :
    (x, y, z) = (0, 5, 2) ∨ (x, y, z) = (1, 3, 3) ∨ (x, y, z) = (2, 1, 4) := by
  -- show that x + y + z = 7
  have eq1 : x + y + z = 7 := by
    -- 3 * x + 3 * y + 3 * z ≤ 30 implies x + y + z ≤ 10
    have ineq1 : x + y + z ≤ 10 := by linarith
    -- 30 ≤ 5 * x + 5 * y + 5 * z implies 6 ≤ x + y + z
    have ineq2 : 6 ≤ x + y + z := by linarith
    -- so x + y + z = 6, 7, 8, 9, or 10
    -- the only prime number is 7
    interval_cases x + y + z <;> norm_num at h₁ ⊢
  -- we get x + 2 = z
  have hx : x + 2 = z := by linarith
  -- we get y + 2 * z = 9
  have hy : y + 2 * z = 9 := by linarith
  -- we get 2 ≤ z ≤ 4
  have hz1 : 2 ≤ z := by linarith
  have hz2 : z ≤ 4 := by linarith
  -- consider all possible values of z (2, 3, 4) and find corresponding values of x and y
  interval_cases z
  · rw [show x = 0 by linarith, show y = 5 by linarith]
    trivial
  · rw [show x = 1 by linarith, show y = 3 by linarith]
    trivial
  · rw [show x = 2 by linarith, show y = 1 by linarith]
    trivial