import Mathlib

theorem number_theory_15892 : IsGreatest {m | m ∈ Finset.Icc 1000 9999 ∧ 45 ∣ m ∧ 7 ∣ m ∧ 45 ∣ Nat.ofDigits 10 (Nat.digits 10 m).reverse } 5985 := by
  constructor
  · -- First, show that 5985 is in the set.
    constructor
    · -- Show 5985 is in the range [1000, 9999].
      norm_num [Finset.mem_Icc]
    constructor
    · -- Show 45 divides 5985.
      norm_num
    constructor
    · -- Show 7 divides 5985.
      norm_num
    · -- Show 45 divides the reverse of 5985 (which is 5895).
      native_decide
  · -- Now, we need to show that for any m in the set, m ≤ 5985.
    intro m hm
    rcases hm with ⟨hm1, hm2, hm3, hm4⟩
    rw [Finset.mem_Icc] at hm1
    rcases hm1 with ⟨hm1l, hm1u⟩
    by_contra h
    push_neg at h
    interval_cases m <;> norm_num [Nat.ofDigits] at hm2 hm3 hm4 ⊢
    <;> try { contradiction }