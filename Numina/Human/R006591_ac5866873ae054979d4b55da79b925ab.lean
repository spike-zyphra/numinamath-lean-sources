import Mathlib

open Finset

lemma sum_range_eq_sum_Icc (n : ℕ) : ∑ i ∈ range (n + 1), i = ∑ i ∈ Icc 1 n, i := by
  have aux : range (n + 1) = insert 0 (Icc 1 n) := by 
    refine Finset.ext_iff.mpr ?_
    intro x
    constructor
    · simp
      intro hx
      by_cases hx0 : x = 0
      · left
        exact hx0
      · right
        omega
    · simp
      intro hx
      omega
  rw [aux, sum_insert]
  simp
  simp

theorem number_theory_638943 (M : ℕ) (hM : M > 0) :
  (∑ i ∈ Finset.Icc 1 (M + 2), i) % M = if Even M then (M / 2 + 3) % M else 3 % M := by 
  rw [←sum_range_eq_sum_Icc, sum_range_id]
  simp
  by_cases even_m : Even M
  · -- the cases M is even
    rw [if_pos even_m]
    obtain ⟨k, hk⟩ := even_m
    have aux1 : M / 2 = k := by 
      rw [hk]
      omega
    rw [aux1]
    have aux2 : (M + 2 + 1) * (M + 2) = (2 * k + 3) * (k + 1) * 2 := by 
      rw [hk]
      ring
    rw [aux2]
    simp
    apply Eq.symm
    -- mod eq iff the difference is divible by M.
    apply Nat.modEq_of_dvd 
    norm_num
    ring_nf
    rw [hk]
    simp
    use ((2 : ℤ) + k)
    ring_nf
  · -- the case M is odd
    rw [if_neg even_m]
    simp at even_m
    obtain ⟨k, hk⟩ := even_m
    have aux1 : (M + 2 + 1) * (M + 2) = (2 * k + 3) * (k + 2) * 2 := by 
      rw [hk]
      ring
    rw [aux1]
    simp
    apply Eq.symm
    -- mod eq iff the difference is divible by M.
    apply Nat.modEq_of_dvd
    rw [hk]
    ring_nf
    norm_num
    use ((k : ℤ) + 3)
    ring