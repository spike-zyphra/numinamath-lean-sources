import Mathlib

theorem algebra_184364 (f : ℕ → ℤ) (hf : f 0 = 1 ∧ f 1 = 3 ∧ ∀ n, f (n + 2) = f (n + 1) - f n) : ∑ i in Finset.range 100, f i = 5 := by
  rcases hf with ⟨f0, f1, f2⟩
  norm_num [Finset.sum_range_succ, f0, f1, f2]
  <;> try omega