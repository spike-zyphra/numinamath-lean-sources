import Mathlib

/- Galperin G.A.

I

$\frac{\text{ Prove that }}{2+\frac{1}{3+\frac{1}{4+\frac{1}{\ddots}+\frac{1}{1991}}}}+\frac{1}{1+\frac{1}{1+\frac{1}{3+\frac{1}{4+\frac{1}{\ddots}+\frac{1}{1991}}}}}=1$. -/
theorem algebra_216222 {f : ℕ → ℚ} (h : f 1991 = 1991) (hn : ∀ n, f n = 1 / (n + f (n + 1))) :
  f 2 + 1 / (1 + 1 / (1 + f 3)) = 1 := by
  -- show that f 3 is positive, so we don't run into any issues rearranging
  have pos : ∀ n ≤ 1991, f n > 0
  · intro n hn
    induction hn using Nat.decreasingInduction with
    | self => rw [h]; trivial
    | of_succ k hk ih => rw [hn]; positivity
  -- rearrange and conclude
  rw [hn 2, show 2 + 1 = 3 by trivial]
  have h3_le : 3 ≤ 1991
  · trivial
  have pos1 : 1 + f 3 > 0
  · linarith [pos _ h3_le]
  have pos3 : 2 + f 3 > 0
  · linarith [pos _ h3_le]
  field_simp
  ring