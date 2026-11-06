import Mathlib

open Real Set

/-Determine the remainder when 1+2+⋯+2014 is divided by 2012 -/
theorem number_theory_608903: (∑ i ∈ Icc 1 2014, i) % 2012 = 1009 := by
  have sum: ∀ n: ℕ, ∑ i ∈ Icc 1 n, i = (n * (n + 1)) / 2 := by
    intro n
    induction' n with n h
    . simp
    . simp [Finset.sum_Icc_succ_top]
      rw [show ∑ i ∈ (Icc 1 n).toFinset, i =  ∑ k ∈ Finset.Icc 1 n, k by simp] at h
      rw [h]
      rw [Mathlib.Tactic.Zify.natCast_eq]
      field_simp
      ring_nf
      omega
  specialize sum 2014
  simp at sum
  simp [sum]