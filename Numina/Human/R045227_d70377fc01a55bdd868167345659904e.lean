import Mathlib

/- In an equation of the form $k = ax^2 + bx + c$ with $a > 0$, the least possible value of $k$ occurs at $x = -b/(2a)$. In the equation $k = (6x + 12)(x - 8)$, what is the least possible value for $k$? -/
theorem algebra_20173 {k : ℝ → ℝ} (hk : k = fun x => (6 * x + 12) * (x - 8)) :
    IsLeast (Set.range k) (-150) := by
  have h : ∀ x : ℝ, (6 * x + 12) * (x - 8) = 6 * (x - 3) ^ 2 - 150 := by
    intro x
    ring
  constructor
  · -- k(3) = -150
    use 3
    rw [hk]
    ring
  · -- k(x) ≥ -150 for all x
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [hx.symm, hk]
    simp only
    rw [h]
    -- 0 ≤ 6 * (x - 3) ^ 2, so k(x) ≥ -150
    have : 0 ≤ 6 * (x - 3) ^ 2 := by
      apply mul_nonneg
      exact Nat.ofNat_nonneg' 6
      exact sq_nonneg (x - 3)
    linarith
