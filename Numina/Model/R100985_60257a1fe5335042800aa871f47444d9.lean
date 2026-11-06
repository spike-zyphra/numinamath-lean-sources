import Mathlib

theorem number_theory_11075 (f : ℕ → ℕ) (hf : ∀ n, f n = 3 * n ^ 2 - 3 * n + 1) :
    (∑ i in Finset.Icc 1 2010, f i) % 10000 = 1000 := by
  simp_rw [hf]
  native_decide