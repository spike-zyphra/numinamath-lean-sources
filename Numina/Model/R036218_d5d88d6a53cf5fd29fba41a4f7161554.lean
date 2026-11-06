import Mathlib
theorem algebra_608747 (f : ℝ → ℝ → ℝ) (hf : f = fun x y => x ^ 2 + 2 * x + y ^ 2 + 4 * y) : IsLeast {S : ℝ | ∃ x y : ℝ, S = f x y + f (x + 1) y + f x (y + 1) + f (x + 1) (y + 1)} (-18):= by
  constructor
  · -- Let's prove that -18 is in the set
    use -3 / 2, -5 / 2
    simp [hf]
    norm_num
  · -- Let's prove that -18 is the least value in the set
    intro S hS
    rcases hS with ⟨x, y, hS⟩
    have h1 : f x y + f (x + 1) y + f x (y + 1) + f (x + 1) (y + 1) ≥ -18 := by
      simp [hf]
      nlinarith [sq_nonneg (x + 3 / 2), sq_nonneg (y + 5 / 2), sq_nonneg (x + 3 / 2 - (y + 5 / 2)), sq_nonneg (x - y)]
    linarith [hS, h1]