import Mathlib

open Finset

def H : ℕ → ℚ := fun n => ∑ k ∈ Icc 1 n, 1 / (k : ℚ) 

lemma sum_alter_harmonic (n : ℕ) (hn : n ≥ 1) : 
  ∑ k ∈ Icc 1 (2 * n), (-1 : ℚ) ^ (k + 1) / k = H (2 * n) - H n := by 
  induction' hn with m ih1 ih2
  · simp
    unfold H
    simp
    have eq_aux : Icc 1 2 = {1, 2} := by rfl
    simp [eq_aux]
    norm_num
  · simp
    have seteq1 : Icc 1 (2 * (m + 1)) = insert (2 * (m + 1)) (Icc 1 (2 * m + 1)) := by 
      refine Eq.symm (Nat.Icc_insert_succ_right ?_)
      linarith
    have seteq2 : (Icc 1 (2 * m + 1)) = insert (2 * m + 1) (Icc 1 (2 * m)) := by
      refine Eq.symm (Nat.Icc_insert_succ_right ?_)
      linarith
    have seteq3 : Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) := by 
      refine Eq.symm (Nat.Icc_insert_succ_right ?_)
      linarith
    rw [seteq1, sum_insert, seteq2, sum_insert]
    simp [ih2]
    have aux1 : H (2 * (m + 1)) = H (2 * m + 1) + 1 / ((2 * (m + 1)) : ℚ) := by
      unfold H
      rw [seteq1, sum_insert]
      norm_num
      ring_nf
      simp
      intro h1
      linarith
    have aux2 : H (2 * m + 1) = H (2 * m) + 1 / ((2 * m + 1): ℚ) := by
      unfold H
      rw[seteq2, sum_insert]
      norm_num
      ring_nf
      simp
    have aux3 : H (m + 1) = H m + 1 / ((m+1): ℚ) := by
      unfold H
      rw [seteq3, sum_insert]
      norm_num
      ring_nf
      simp
    have aux4 : (-1 : ℚ) ^ (2 * (m + 1) + 1) = -1 := by 
      rw [pow_add]
      simp
    have aux5 : (-1 : ℚ) ^ (2 * m + 1 + 1) = 1:= by
      rw [pow_add, pow_add]
      simp
    have aux6 : 1 / ((m : ℚ) + 1) = 2 * (1 / (2 * (m + 1))) := by 
      field_simp
    rw [aux1, aux2, aux3, aux4, aux5, aux6]
    ring_nf
    simp
    simp
    intro h1 
    linarith

lemma sum_alter (n : ℕ): (n ≥ 1) → ∑ j ∈ Icc 2 (2 * n), (- 1 : ℚ) ^ j = 1 := by 
  intro hn
  induction' hn with m ih1 ih2
  · simp 
  · simp 
    have seteq1 : Icc 2 (2 * (m + 1)) = insert (2 * (m + 1)) (Icc 2 (2 * m + 1)) := by 
      refine Eq.symm (Nat.Icc_insert_succ_right ?_)
      linarith
    have seteq2 : (Icc 2 (2 * m + 1)) = insert (2 * m + 1) (Icc 2 (2 * m)) := by
      refine Eq.symm (Nat.Icc_insert_succ_right ?_)
      simp at ih1
      linarith
    rw [seteq1, sum_insert, seteq2, sum_insert]
    simp [ih2, pow_add]
    simp
    simp
    linarith

theorem number_theory_638038 (m : ℕ) (hm : 0 < m) :
  ∑ i ∈ Finset.range (2 * m - 1), (-1 : ℤ)^i * (2 * m - 1 - i) / (i + 2 : ℚ) =
  ∑ i ∈ Finset.range m, (2 * i + 1) / (m + 1 + i : ℚ) := by 
  have h3 : ∑ i ∈ Finset.range (2 * m - 1), (-1 : ℤ)^i * (2 * m - 1 - i) / (i + 2 : ℚ)
    = ∑ j ∈ Icc 2 (2 * m), (-1) ^ j * ((2 * m + 1 : ℚ) / j - 1) := by 
    let t : ℕ → ℕ := fun n => n + 2
    let s : ℕ → ℕ := fun n => n - 2 
    refine sum_nbij' t s ?_ ?_ ?_ ?_ ?_
    · simp 
      intro i hi
      unfold t
      omega
    · simp 
      unfold s
      omega
    · simp
      unfold t s
      omega
    · simp 
      unfold t s
      omega
    · simp 
      intro i hi
      unfold t 
      simp
      have neq1 : (i : ℚ) + 2 ≠ 0 := by
        norm_cast
      field_simp
      ring
  have h4 : ∑ j ∈ Icc 2 (2 * m), (-1) ^ j * ((2 * m + 1 : ℚ) / j - 1) = 
    (2 * m + 1) * ∑ j ∈ Icc 2 (2 * m), (- 1 : ℚ) ^ j / j - ∑ j ∈ Icc 2 (2 * m), (- 1 : ℚ) ^ j := by 
    rw [mul_sum, ←sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    simp at hi
    have ineq : (i : ℚ) ≠ 0 := by 
      norm_cast
      linarith 
    field_simp
    ring
  have h5 (n : ℕ): (n ≥ 1) → ∑ j ∈ Icc 2 (2 * n), (- 1 : ℚ) ^ j = 1 := by 
    intro hn
    exact sum_alter n hn
  have h6 : ∑ j ∈ Icc 2 (2 * m), (- 1 : ℚ) ^ j / j = 1 - (H (2 * m) - H m) := by 
    rw [←sum_alter_harmonic m (by linarith)]
    have seteq : Icc 1 (2 * m) = insert 1 (Icc 2 (2 * m)) := by 
      refine Eq.symm (Nat.Icc_insert_succ_left ?_)
      linarith
    rw [seteq, sum_insert]
    simp
    have aux : -∑ x ∈ Icc 2 (2 * m), (-1) ^ (x + 1) / (x : ℚ) = 
      ∑ x ∈ Icc 2 (2 * m), (-1) ^ (x) / (x : ℚ) := by 
      calc 
        _ = - ∑ x ∈ Icc 2 (2 * m), (-1) * ((-1) ^ x / (x : ℚ)) := by 
          rw [neg_inj]
          apply sum_congr rfl
          intro i hi
          simp [pow_add]
          ring
        _ = _ := by 
          simp
    rw [aux]
    simp
  have h1 : ∑ i ∈ Finset.range (2 * m - 1), (-1 : ℤ)^i * (2 * m - 1 - i) / (i + 2 : ℚ)
    = 2 * m - (2 * m + 1) * (H (2 * m) - H m) := by   
    rw [h3, h4, h5 m (by linarith), h6]
    ring_nf
  have h7 : ∑ i ∈ Finset.range m, (2 * i + 1) / (m + 1 + i : ℚ) = ∑ k ∈ Icc (m + 1) (2 * m), (2 - (2 * m + 1: ℚ) / k) := by 
    let t : ℕ → ℕ := fun n => n - (m + 1)
    let s : ℕ → ℕ := fun n => n + (m + 1)
    refine sum_nbij' s t ?_ ?_ ?_ ?_ ?_
    · simp
      intro i hi
      unfold s
      omega
    · simp
      intro i hi1 hi2
      unfold t
      omega
    · simp
      intro i hi
      unfold t s
      omega
    · simp
      intro i hi1 hi2
      unfold t s 
      omega
    · simp 
      intro i hi
      unfold s
      simp
      have neq : ((m : ℚ) + 1 + ↑i) ≠ 0 := by 
        norm_cast
        linarith
      field_simp
      ring_nf
  have h8 : ∑ k ∈ Icc (m + 1) (2 * m), (2 - (2 * m + 1: ℚ) / k) = ∑ k ∈ Icc (m + 1) (2 * m), 2 - (2 * m + 1) * ∑ k ∈ Icc (m + 1) (2 * m), (1 : ℚ)/ k := by
    rw [mul_sum, ←sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    simp at hi
    have ineq : (i : ℚ) ≠ 0 := by 
      norm_cast
      linarith
    field_simp
  have h9 : ∑ k ∈ Icc (m + 1) (2 * m), (1 : ℚ)/ k =  H (2 * m) - H m := by
    have seteq : Icc (m + 1) (2 * m) = (Icc 1 (2 * m)) \ (Icc 1 m) := by 
      refine Finset.ext_iff.mpr ?_
      intro i 
      constructor
      · simp 
        intro hi1 hi2
        omega
      · simp
        omega
    have subset1 : Icc 1 m ⊆ (Icc 1 (2 * m)) := by 
      refine Icc_subset_Icc_right ?_
      linarith
    rw [seteq, sum_sdiff_eq_sub subset1]
    unfold H
    rfl
  have h2 : ∑ i ∈ Finset.range m, (2 * i + 1) / (m + 1 + i : ℚ) = 2 * m - (2 * m + 1) * (H (2 * m) - H m) := by
    rw [h7, h8, h9]
    have aux : ∑ k ∈ Icc (m + 1) (2 * m), (2 : ℚ) = 2 * m := by 
      norm_cast
      rw [sum_const]
      simp 
      omega
    rw [aux]
  rw [h1, h2]