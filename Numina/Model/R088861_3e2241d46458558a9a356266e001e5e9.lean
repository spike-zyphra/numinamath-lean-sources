import Mathlib

open Real
open scoped BigOperators

theorem inequalities_191549 (n : ℕ) :
  ∏ i ∈ Finset.Icc 1 n, (1 + 1 / (i^2 + 2 * i : ℝ)) < 2 := by
  have h1 : ∀ (n : ℕ), ∏ i ∈ Finset.Icc 1 n, (1 + 1 / (i^2 + 2 * i : ℝ)) = (2 * (n + 1 : ℝ) / (n + 2 : ℝ)) := by
    intro n
    induction n with
    | zero =>
      simp
      <;> norm_num
    | succ n ih =>
      rw [Finset.prod_Icc_succ_top (by linarith)]
      rw [ih]
      field_simp
      ring_nf
      <;> norm_num
      <;> ring
  have h2 := h1 n
  rw [h2]
  have h3 : (n + 2 : ℝ) > 0 := by
    have h4 : (n : ℝ) ≥ 0 := by exact_mod_cast Nat.zero_le n
    linarith
  have h5 : (2 * (n + 1 : ℝ) / (n + 2 : ℝ)) < (2 : ℝ) := by
    have h6 : (n + 2 : ℝ) > 0 := by
      have h4 : (n : ℝ) ≥ 0 := by exact_mod_cast Nat.zero_le n
      linarith
    apply (div_lt_iff h6).mpr
    linarith
  linarith