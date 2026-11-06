import Mathlib

theorem number_theory_174164 (n : ℕ) :
    n ∈ {n | n ∈ Finset.Icc 100 999 ∧ (Nat.digits 10 n).prod = 5 * (Nat.digits 10 n).sum} ↔
    n = 257 ∨ n = 275 ∨ n = 527 ∨ n = 572 ∨ n = 725 ∨ n = 752 ∨
      n = 345 ∨ n = 354 ∨ n = 435 ∨ n = 453 ∨ n = 534 ∨ n = 543 := by
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Assume n is a 3-digit number with digit product = 5*(digit sum), show it's in the boxed set
    intro h
    rcases h with ⟨hn, h1⟩
    rw [Finset.mem_Icc] at hn
    rcases hn with ⟨h100, h999⟩
    interval_cases n <;> norm_num at h1 ⊢ <;> omega
  · -- Assume n is in the boxed set, show it's a 3-digit number with digit product = 5*(digit sum)
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · -- n = 257
      constructor
      · norm_num
      · -- Show digit product equals 5 * digit sum
        norm_num
    · -- n = 275
      constructor
      · norm_num
      · -- Show digit product equals 5 * digit sum
        norm_num
    · -- n = 527
      constructor
      · norm_num
      · -- Show digit product equals 5 * digit sum
        norm_num
    · -- n = 572
      constructor
      · norm_num
      · -- Show digit product equals 5 * digit sum
        norm_num
    · -- n = 725
      constructor
      · norm_num
      · -- Show digit product equals 5 * digit sum
        norm_num
    · -- n = 752
      constructor
      · norm_num
      · -- Show digit product equals 5 * digit sum
        norm_num
    · -- n = 345
      constructor
      · norm_num
      · -- Show digit product equals 5 * digit sum
        norm_num
    · -- n = 354
      constructor
      · norm_num
      · -- Show digit product equals 5 * digit sum
        norm_num
    · -- n = 435
      constructor
      · norm_num
      · -- Show digit product equals 5 * digit sum
        norm_num
    · -- n = 453
      constructor
      · norm_num
      · -- Show digit product equals 5 * digit sum
        norm_num
    · -- n = 534
      constructor
      · norm_num
      · -- Show digit product equals 5 * digit sum
        norm_num
    · -- n = 543
      constructor
      · norm_num
      · -- Show digit product equals 5 * digit sum
        norm_num