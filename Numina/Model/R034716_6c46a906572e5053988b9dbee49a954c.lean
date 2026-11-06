import Mathlib

theorem number_theory_611337 {s : Set ℕ} (hs : s = {x : ℕ | 1 < x ∧ 1000 ∣ x ^ 2 - x}) :
    IsLeast s 376 := by
  rw [IsLeast]
  constructor
  · -- Show 376 ∈ s
    rw [hs]
    constructor
    · -- Show 1 < 376
      norm_num
    · -- Show 1000 ∣ 376^2 - 376
      norm_num
  · -- Show there is no smaller element in s
    intro n hn
    rw [hs] at hn
    rcases hn with ⟨hn1, hn2⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn2 <;> omega