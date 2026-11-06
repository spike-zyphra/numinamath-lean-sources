import Mathlib

theorem algebra_246806 (f : ℕ → ℤ) (hf : ∀ n, f n = ∑ i in Finset.Icc 1 n, i) :
    ∀ n, f n = n * (n + 1) / 2 := by
  intro n
  induction n with 
  | zero => 
    simp [hf]
  | succ n ih =>
    calc 
      f (n + 1) = f n + (n + 1) := by 
        rw [hf (n + 1), hf n]
        simp [Finset.sum_Icc_succ_top, add_comm]
      _ = n * (n + 1) / 2 + (n + 1) := by rw [ih]
      _ = (n * (n + 1) + 2 * (n + 1)) / 2 := by 
        omega
      _ = (n + 1) * (n + 2) / 2 := by 
        ring