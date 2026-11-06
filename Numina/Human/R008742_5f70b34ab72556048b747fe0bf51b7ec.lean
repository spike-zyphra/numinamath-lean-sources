import Mathlib

open Finset Real Nat
/-Compute ∑ k ∈ Icc 1 2009, k * ([2009 / k] - [2008 / k])-/
theorem number_theory_608524: ∑ k ∈ Icc 1 2009, k * (2009 / k - 2008 / k) = 2394 := by
-- prove the key lemma --
  have h1: ∀ k ∈ Icc 1 2009, ¬ k ∣ 2009 →  2009 / k - 2008 / k = 0 := by
    intro k hk h
    simp at hk
    set a:= 2009 / k with ha
    set b:= 2009 % k with hb
    have lb: 1 ≤ b := by
      by_contra! no
      replace no: b = 0 := by
        omega
      simp [no] at hb
      symm at hb
      replace hb: k ∣ 2009 := by
        omega
      tauto
    have l: 2009 = a * k + b := by
      simp only [ha,hb]
      symm
      rw [show 2009 / k * k = k * (2009 / k) by ring]
      apply Nat.div_add_mod
    have pos: 2008 / k ≤ a := by
      rw [ha]
      apply Nat.div_le_div_right
      norm_num
    have neg: a ≤ 2008 / k := by
      have o: a * k ≤ 2008 := by
        have i: a * k = 2009 - b := by
          rw [show a * k = a * k + b - b by omega]
          rw [l]
        rw [i]
        rw [show 2008 = 2009 - 1 by omega]
        apply Nat.sub_le_sub_left
        exact lb
      replace o: a * k / k ≤ 2008 / k := by
        apply Nat.div_le_div_right
        exact o
      rw [show a * k / k = a by apply Nat.mul_div_cancel; omega] at o
      exact o
    have j: a = 2008 / k := by omega
    rw [j]
    simp
    -- find the divisors of 2009--
  have div: Nat.divisors 2009 = {1, 7, 41, 49, 287, 2009} := by
    native_decide
    -- evaluate the splitted sums respectly --
  have eq1: ∑ k ∈ Icc 288 2008, k * (2009 / k - 2008 / k) = 0 := by
    have nedvd: ∀ k ∈ Icc 288 2008, ¬ k ∣ 2009 := by
     intro k hk
     simp at hk
     by_contra! no
     replace no: k ∈ Nat.divisors 2009 := by
       simp
       omega
     rw [div] at no
     absurd no
     by_contra! isin
     simp at isin
     omega
    have zero1: ∀ k ∈ Icc 288 2008, k * (2009 / k - 2008 / k) = 0 := by
      intro k hk
      specialize nedvd k hk
      specialize h1 k
      simp at hk
      have o: (2009 / k - 2008 / k) = 0 := by
        apply h1
        simp
        omega
        exact nedvd
      rw [o]
      omega
    rw [Finset.sum_eq_card_nsmul zero1]
    simp
  have eq2: ∑ k ∈ Icc 50 286, k * (2009 / k - 2008 / k) = 0 := by
    have nedvd: ∀ k ∈ Icc 50 286, ¬ k ∣ 2009 := by
        intro k hk
        simp at hk
        by_contra! no
        replace no: k ∈ Nat.divisors 2009 := by
          simp
          omega
        rw [div] at no
        absurd no
        by_contra! isin
        simp at isin
        omega
    have zero2: ∀ k ∈ Icc 50 286, k * (2009 / k - 2008 / k) = 0 := by
      intro k hk
      specialize nedvd k hk
      specialize h1 k
      simp at hk
      have o: (2009 / k - 2008 / k) = 0 := by
        apply h1
        simp
        omega
        exact nedvd
      rw [o]
      omega
    rw [Finset.sum_eq_card_nsmul zero2]
    simp
  have eq3: ∑ k ∈ Icc 1 49, k * (2009 / k - 2008 / k) = 98 := by
    simp [Finset.sum_Icc_succ_top]
  have sum1: ∑ k ∈ Icc 1 2009, k * (2009 / k - 2008 / k)
  = ∑ k ∈ Icc 1 2008, k * (2009 / k - 2008 / k) + 2009 := by
    rw [Finset.sum_Icc_succ_top]
    norm_num
  have sum2: ∑ k ∈ Icc 1 2008, k * (2009 / k - 2008 / k)
  = ∑ k ∈ Icc 1 287, k * (2009 / k - 2008 / k) + ∑ k ∈ Icc 288 2008, k * (2009 / k - 2008 / k) := by
      have h_disjoint : Disjoint (Icc 1 287) (Icc 288 2008) := by
        simp [disjoint_iff_inter_eq_empty]
        ext x
        simp
        omega
      have h_union : Icc 1 287 ∪ Icc 288 2008 = Icc 1 2008 := by
        ext x
        simp only [mem_union, mem_Icc]
        omega
  -- Apply the sum over union property
      rw [← h_union, sum_union h_disjoint]
  have sum3: ∑ k ∈ Icc 1 287, k * (2009 / k - 2008 / k)
  = ∑ k ∈ Icc 1 286, k * (2009 / k - 2008 / k) + 287 := by
    rw [Finset.sum_Icc_succ_top]
    norm_num
  have sum4: ∑ k ∈ Icc 1 286, k * (2009 / k - 2008 / k)
  = ∑ k ∈ Icc 1 49, k * (2009 / k - 2008 / k) + ∑ k ∈ Icc 50 286, k * (2009 / k - 2008 / k) := by
      have h_disjoint : Disjoint (Icc 1 49) (Icc 50 286) := by
        simp [disjoint_iff_inter_eq_empty]
        ext x
        simp
        omega
      have h_union : Icc 1 49 ∪ Icc 50 286 = Icc 1 286 := by
        ext x
        simp only [mem_union, mem_Icc]
        omega
      rw [← h_union, sum_union h_disjoint]
  -- plug the results into the target --
  rw [eq3,eq2] at sum4
  rw [show 98 + 0 = 98 by norm_num] at sum4
  rw [sum4] at sum3
  clear sum4
  rw [eq1,sum3] at sum2
  clear sum3 eq1 eq2 eq3
  rw [sum2] at sum1
  rw [sum1]
