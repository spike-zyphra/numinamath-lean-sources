import Mathlib

open Finset

theorem number_theory_290095 :
    IsLeast {A | (∃ a b, a ∈ Icc 10 99 ∧ b ∈ Icc 10 99 ∧ A = a * b) ∧ A ∈ Icc 1000 9999
      ∧ (∃ x y, Nat.digits 10 A = [x, x, y, y]) ∧ 51 ∣ A} 1122 := by 
  constructor
  · -- Show 1122 is in the set
    constructor
    · -- Show 1122 is a product of two two-digit numbers
      use 51, 22
      simp
    constructor
    · -- Show 1122 is in the range [1000, 9999]
      native_decide
    constructor
    · -- Show the digits of 1122 are [2, 2, 1, 1]
      use 2, 1
      native_decide
    · -- Show 1122 is divisible by 51
      norm_num
  · -- Prove 1122 is minimal
    intro A h 
    rcases h with ⟨⟨a, b, ha, hb, hprod⟩, hA, hdigits, hdiv⟩
    rw [mem_Icc] at ha hb hA
    rcases ha with ⟨ha1, ha2⟩
    rcases hb with ⟨hb1, hb2⟩
    rcases hdigits with ⟨x, y, h1⟩
    by_contra h
    push_neg at h
    have h2 : A < 1122 := h
    interval_cases A <;> norm_num [hprod] at *
    <;> norm_num at h1 hdiv <;> omega