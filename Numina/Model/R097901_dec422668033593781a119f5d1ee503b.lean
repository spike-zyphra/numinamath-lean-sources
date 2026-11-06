import Mathlib

theorem algebra_246659 (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, (i / (Nat.factorial (i + 1) : ℚ)) =
    ((Nat.factorial (n + 1) - 1) / (Nat.factorial (n + 1) : ℚ)) := by
  induction n with
  | zero =>
    -- Base case n = 0, sum from 1 to 0 which is empty, so 0
    -- (Nat.factorial (0 + 1) - 1) / (Nat.factorial (0 + 1) : ℚ) = (Nat.factorial 1 - 1) / (Nat.factorial 1 : ℚ) = (1 - 1) / (1 : ℚ) = 0
    simp [Finset.sum_eq_zero, Nat.factorial]
  | succ n ih =>
    -- Inductive step
    -- Using the induction hypothesis for n, prove the statement for n+1
    rw [Finset.sum_Icc_succ_top (by norm_num)]
    rw [ih]
    field_simp [Nat.factorial] at *
    ring_nf
    <;> simp [Nat.factorial] at *
    <;> ring_nf
    <;> field_simp [Nat.factorial]
    <;> ring