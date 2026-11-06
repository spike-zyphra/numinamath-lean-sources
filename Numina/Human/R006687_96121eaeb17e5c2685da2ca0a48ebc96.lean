import Mathlib

open Finset

-- proving the lemma for the harmonic series `∀ n, ∑ i ∈ Icc (1 : ℕ) (2 ^ n), (1 / (i : ℝ)) ≥ 1 + n / 2`
lemma harmonic_series_ge (n : ℕ) : 
  ∑ i ∈ Icc (1 : ℕ) (2 ^ n), (1 / (i : ℝ)) ≥ 1 + n / 2 := by 
  induction n with 
  | zero => 
    simp
  | succ k ih => 
    have disj1 : Disjoint (Icc 1 (2 ^ k)) (Icc (2 ^ k + 1) (2 ^ (k + 1))) := by 
      refine disjoint_left.mpr ?_
      simp
      intro i hi1 hi2 hi3
      omega
    have seteq : Icc 1 (2 ^ (k + 1)) = (Icc 1 (2 ^ k)).disjUnion (Icc (2 ^ k + 1) (2 ^ (k + 1))) disj1 := by 
      simp
      refine Finset.ext_iff.mpr ?_
      simp
      omega
    rw [seteq, sum_disjUnion]
    have ineq_aux : ∑ x ∈ Icc (2 ^ k + 1 : ℕ) (2 ^ (k + 1)), 1 / (x : ℝ) ≥ 1 / 2 := by 
      calc 
        _ ≥ ∑ x ∈ Icc (2 ^ k + 1 : ℕ) (2 ^ (k + 1)), 1 / (2 ^ (k + 1) : ℝ) := by 
          apply sum_le_sum
          simp 
          intro i hi1 hi2
          refine inv_anti₀ ?_ ?_
          norm_cast
          have aux1 : 2 ^ k + 1 > 0 := by 
            positivity
          linarith 
          norm_cast
        _ = _ := by 
          rw [sum_const]
          simp
          rw [Nat.cast_sub]
          norm_num
          field_simp
          ring
          rw [pow_add]
          simp
    calc 
      _ ≥ 1 + (k : ℝ) / 2 + 1 / 2 := by 
        linarith
      _ = _ := by 
        norm_num
        field_simp
        ring

theorem number_theory_640164 (M : ℝ) (hM : M > 0) :
  ∑ n ∈ Finset.Icc (1 : ℕ) (2 ^ ⌈2 * M⌉₊), (1 / n : ℝ) > M := by 
  obtain h1 := harmonic_series_ge (⌈2 * M⌉₊)
  have ineq_aux : ↑⌈2 * M⌉₊ / (2 : ℝ) > M - 1 := by 
    refine (lt_div_iff₀ ?_).mpr ?_ 
    linarith
    have eq_aux :( ⌈2 * M⌉₊ : ℝ) = ⌈2 * M⌉ := by 
      norm_cast
      refine Int.natCast_ceil_eq_ceil ?_
      linarith
    rw [eq_aux]
    have ineq_aux2 : (⌈2 * M⌉ : ℝ) ≥ 2 * M := by 
      exact Int.le_ceil (2 * M)
    have ineq_aux3 : 2 * M ≥ (M - 1) * 2 := by 
      linarith
    linarith
  linarith