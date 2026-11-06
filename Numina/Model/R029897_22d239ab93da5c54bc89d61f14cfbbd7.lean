import Mathlib

theorem algebra_20876 {f : ℕ → ℤ} (h : ∀ n ≥ 1, f (n + 1) = (-1) ^ (n + 1) * n - 2 * f n)
    (h' : f 1 = f 1986) :
    ∑ i in Finset.range 1985, f (i + 1) = 331 := by
  have key : ∑ i ∈ Finset.range 1985, ((-1 : ℤ) ^ (i + 1 + 1) * (i + 1) - 2 * f (i + 1)) =
      ∑ i ∈ Finset.range 1985, f (i + 1 + 1) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [h (x + 1) (by omega)]
    congr
  have : ∑ i ∈ Finset.range 1985, f (i + 1 + 1) = ∑ i ∈ Finset.range 1985, f (i + 1) := by
    nth_rw 2 [Finset.sum_range_succ']
    rw [zero_add, h', Finset.sum_range_succ]
  rw [this, Finset.sum_sub_distrib, ← Finset.mul_sum] at key
  have h_sum_eq : 3 * (∑ i in Finset.range 1985, f (i + 1)) =
      ∑ i in Finset.range 1985, ((-1 : ℤ) ^ (i + 1 + 1) * (i + 1)) := by
    linarith
  have h_explicit_sum : ∑ i in Finset.range 1985, ((-1 : ℤ) ^ (i + 1 + 1) * (i + 1)) = 993 := by
    native_decide
  rw [h_explicit_sum] at h_sum_eq
  linarith