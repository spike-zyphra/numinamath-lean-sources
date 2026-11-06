import Mathlib

theorem algebra_4465 (x y : ℕ → ℤ) (hx : ∀ n, x n = n)
  (hy : ∀ n, y n = |x n - 1009|) :
  ∑ i in Finset.Icc 1 2017, y i = 1017072 := by
  rw [Finset.sum_congr rfl (fun i hi => hy i)]
  rw [Finset.sum_congr rfl (fun i hi => by rw [hx i])]
  native_decide