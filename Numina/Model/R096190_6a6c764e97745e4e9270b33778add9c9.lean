import Mathlib

theorem algebra_115964 (n : ℕ) :
    ∑ i in Finset.Icc 1 n, (1 / ((i * (i + 1)) : ℚ)) = n / (n + 1 : ℚ) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by norm_num)]
    rw [ih]
    field_simp
    <;> ring