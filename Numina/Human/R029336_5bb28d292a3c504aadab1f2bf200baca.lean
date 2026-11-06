import Mathlib

/- Trouver toutes les fonctions $f$ de $\mathbb{R}$ dans $\mathbb{R}$
telles que pour tous réels $x, y$,
$$
f(x) f(y)=f(x y)+x+y
$$ -/
theorem algebra_604558{f: ℝ → ℝ}:
  ( ∀(x y: ℝ), (f x)*(f y) = f (x*y) + x + y ) ↔
  ( ∀x, f x = x + 1) := by
  constructor <;> intro h
  · -- take y = 0, f(x)f(0) = f(0)+x by problem statement
    have hy0: ∀x, (f x)*(f 0) = f 0 + x := by
      intro x; simp [h x 0]
    -- take x = 1, easy to get f(0) ≠ 0
    have f0_ne_0: f 0 ≠ 0 := by
      by_contra! hh
      have := hy0 1
      simp [hh] at this
    -- then we can solve f(0) = 1
    have hf0: f 0 = 1 := by
      -- we show this by setting x=0
      have := hy0 0
      simp at this
      exact (mul_eq_right₀ f0_ne_0).mp this
    -- thereby the function turns out to be f(x) = x+1
    simp [hf0] at hy0
    intro x; rw [hy0 x]; ring
  · -- easy to verify f(x) = x+1 satisfy the conditions.
    intro x y
    simp [h x, h y, h (x*y)]
    ring