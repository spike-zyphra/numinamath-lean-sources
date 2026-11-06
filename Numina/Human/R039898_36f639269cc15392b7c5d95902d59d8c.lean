import Mathlib

open Finset

theorem inequalities_232646 {n : ℕ} (hn : 1 < n) :
    ∏ i ∈ Icc 1 n, i ^ i < n ^ (n * (n + 1) / 2) := by
  have h₁ : n ^ (n * (n + 1) / 2) = ∏ i ∈ Icc 1 n, n ^ i := by
    rw [prod_pow_eq_pow_sum]
    congr
    suffices 2 * ∑ i ∈ Icc 1 n, i = n * (n + 1) by omega
    clear hn
    induction n with
    | zero => simp
    | succ n ih =>
      simp [sum_Icc_succ_top, ih, mul_add, ih]
      ring
  rw [h₁]
  apply prod_lt_prod
  . intro i hi
    obtain ⟨hi₁, hi₂⟩ := mem_Icc.mp hi
    positivity
  . intro i hi
    obtain ⟨hi₁, hi₂⟩ := mem_Icc.mp hi
    exact Nat.pow_le_pow_of_le_left hi₂ i
  . use 1
    simp [hn, le_of_lt hn]
