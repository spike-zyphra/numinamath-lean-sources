import Mathlib

open Finset Real Nat

theorem number_theory_635098 (N : ℕ) (hN : 2 ≤ N) :
  ∏ i ∈ Icc 2 N, ((1 : ℝ) - (fib i : ℝ) ^ 2 / (fib (i + 1) : ℝ) ^ 2) = fib (N + 2) / (2 * fib N * fib (N + 1)) := by 
  by_cases hN2 : N = 2 
  · rw [hN2]
    simp
    norm_num
  have hNge : N ≥ 3 := by 
    omega
  have h1 : ∏ i ∈ Icc 2 N, ((1 : ℝ) - (fib i : ℝ) ^ 2 / (fib (i + 1) : ℝ) ^ 2) 
    = ∏ i ∈ Icc 2 N, ((fib (i - 1) * fib (i + 2) : ℝ) / (fib (i + 1) ^ 2)) := by 
    apply prod_congr rfl
    intro i hi
    simp at hi
    have ipos : i + 1 > 0 := by 
      linarith
    have neq : fib (i + 1) ≠ 0 := by 
      have pos1 : fib (i + 1) > 0 := by 
        exact fib_pos.mpr ipos
      linarith
    field_simp
    have aux1 : (fib (i + 1) : ℝ) ^ 2 - (fib i) ^ 2 =  
      (fib (i - 1) * fib (i + 2) : ℝ) := by
      have aux2 : fib (i - 1) = fib (i + 1) - fib (i) := by 
        rw [show i + 1 = i - 1 + 2 by omega, fib_add_two]
        rw [show i - 1 + 1 = i by omega]
        simp
      rw [aux2]
      have aux3 : fib (i + 2) = fib (i + 1) + fib (i) := by 
        rw [fib_add_two]
        ring
      rw [aux3, Nat.cast_sub]
      norm_num
      ring
      exact fib_le_fib_succ
    rw [aux1]
  rw [h1, prod_div_distrib, prod_mul_distrib]
  have eq1 : ∏ x ∈ Icc 2 N, (fib (x + 1) : ℝ) = (∏ x ∈ Icc 2 (N -2), (fib (x + 1) : ℝ))* fib (N) * fib (N + 1) := by
    have seteq1 : Icc 2 N = insert N (Icc 2 (N - 1)) := by 
      nth_rw 1 [show N = N - 1 + 1 by omega]
      nth_rw 2 [show N = N - 1 + 1 by omega]
      refine Eq.symm (Icc_insert_succ_right ?_)
      omega
    have seteq2 : Icc 2 (N - 1) = insert (N - 1) (Icc 2 (N - 2)):= by
      nth_rw 1 2 [show N - 1 = N - 2 + 1 by omega]
      refine Eq.symm (Icc_insert_succ_right ?_)
      omega
    rw [seteq1, prod_insert, seteq2, prod_insert]
    rw [show N - 1 + 1 = N by omega]
    norm_cast
    ring
    simp 
    omega
    simp
    omega
  have neq1 : ∏ x ∈ Icc 2 N, (fib (x + 1) : ℝ) ^ 2  ≠ 0 := by 
    have pos : ∏ x ∈ Icc 2 N, (fib (x + 1) : ℝ) ^ 2 > 0 := by 
      apply prod_pos
      intro i hi
      norm_cast
      simp at hi
      have ipos : i + 1 > 0 := by 
        linarith
      have neq : fib (i + 1) ≠ 0 := by 
        have pos1 : fib (i + 1) > 0 := by 
          exact fib_pos.mpr ipos
        linarith
      exact pow_two_pos_of_ne_zero neq
    linarith
  have neq2 : ((2 : ℝ) * (fib N) * (fib (N + 1))) ≠ 0 := by 
    have pos1 : fib N > 0 := by 
      apply fib_pos.mpr
      linarith
    have pos2 : fib (N + 1) > 0 := by 
      apply fib_pos.mpr
      linarith
    norm_cast
    positivity
  field_simp
  have eq2 : (∏ x ∈ Icc 2 N, (fib (x - 1) : ℝ)) = ∏ x ∈ Icc 0 (N - 2), (fib (x + 1) : ℝ) := by 
    let t : ℕ → ℕ := fun x => x + 2
    let s : ℕ → ℕ := fun x => x - 2
    refine prod_nbij' s t ?_ ?_ ?_ ?_ ?_
    · simp 
      unfold s
      omega
    · simp 
      unfold t
      omega
    · simp 
      unfold t s
      omega
    · simp 
      unfold t s 
      omega
    · simp 
      unfold s
      intro a ha1 ha2
      congr
      omega
  rw [eq2]
  have eq3 : ∏ x ∈ Icc 2 N, (fib (x + 2) : ℝ) = ∏ x ∈ Icc 3 (N + 1), (fib (x + 1) : ℝ) := by 
    let s : ℕ → ℕ := fun x => x + 1
    let t : ℕ → ℕ := fun x => x - 1
    refine prod_nbij' s t ?_ ?_ ?_ ?_ ?_
    · simp 
      unfold s
      omega
    · simp 
      unfold t
      omega
    · simp 
      unfold t s
      omega
    · simp 
      unfold t s 
      omega
    · simp 
  rw [eq3, prod_pow, eq1]
  have eq4 : (∏ x ∈ Icc 0 (N - 2), (fib (x + 1) : ℝ)) = 
    fib 1 * fib 2 * (∏ x ∈ Icc 2 (N - 2), (fib (x + 1) : ℝ)) := by 
    have seteq1 : Icc 0 (N - 2) = insert 0 (insert 1 (Icc 2 (N - 2))) := by
      refine Finset.ext_iff.mpr ?_
      intro i 
      simp 
      omega
    rw [seteq1, prod_insert, prod_insert]
    norm_num
    simp
    simp
  rw [eq4]
  norm_num
  have eq5 : fib 3 * ∏ x ∈ Icc 3 (N + 1), (fib (x + 1) : ℝ) = 
    (∏ x ∈ Icc 2 (N - 2), (fib (x + 1) : ℝ)) * fib (N + 2) * fib (N + 1) * fib (N) := by
    have seteq1 : Icc 2 (N + 1) = insert 2 (Icc 3 (N + 1)) := by 
      refine Eq.symm (Icc_insert_succ_left ?_)
      linarith
    have aux1 : fib 3 * ∏ x ∈ Icc 3 (N + 1), (fib (x + 1) : ℝ) = 
      ∏ x ∈ Icc 2 (N + 1), (fib (x + 1) : ℝ) := by 
      rw [seteq1, prod_insert]
      ring_nf
      simp
    rw [aux1]
    have seteq2 : Icc 2 (N + 1) = insert (N + 1) (Icc 2 N) := by 
      refine Eq.symm (Icc_insert_succ_right ?_)
      linarith 
    have seteq3 : Icc 2 N = insert N (Icc 2 (N - 1)) := by 
      nth_rw 1 [show N = N - 1 + 1 by omega]
      nth_rw 2 [show N = N - 1 + 1 by omega]
      refine Eq.symm (Icc_insert_succ_right ?_)
      omega
    have seteq4 : Icc 2 (N - 1) = insert (N - 1) (Icc 2 (N - 2)):= by
      nth_rw 1 2 [show N - 1 = N - 2 + 1 by omega]
      refine Eq.symm (Icc_insert_succ_right ?_)
      omega
    rw [seteq2, prod_insert, seteq3, prod_insert, seteq4, prod_insert]
    rw [show N - 1 + 1 = N by omega, show N + 1 + 1 = N + 2 by omega]
    norm_cast
    ring
    simp
    omega
    simp
    omega
    simp
  have eq6 : ((∏ x ∈ Icc 2 (N - 2), ↑(fib (x + 1))) * ∏ x ∈ Icc 3 (N + 1), ↑(fib (x + 1))) * (2 * ↑(fib N) * ↑(fib (N + 1))) =  (∏ x ∈ Icc 2 (N - 2), (fib (x + 1) : ℝ)) * ((fib 3 : ℝ) * ∏ x ∈ Icc 3 (N + 1), ↑(fib (x + 1))) * ((fib N : ℝ) * (fib (N + 1) : ℝ)) := by 
    norm_num
    ring
  rw [eq6, eq5]
  ring