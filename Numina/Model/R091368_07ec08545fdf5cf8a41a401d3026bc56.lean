import Mathlib

theorem number_theory_153905 (n : ℕ) :
    n ∈ Finset.Icc 1 100 ∧ Odd (n.divisors.card) ↔
    n = 1 ∨ n = 4 ∨ n = 9 ∨ n = 16 ∨ n = 25 ∨ n = 36 ∨
      n = 49 ∨ n = 64 ∨ n = 81 ∨ n = 100 := by
  constructor
  · -- Forward direction: given n in range 1 ≤ n ≤ 100 with Odd (n.divisors.card), 
    -- prove n is a perfect square in the listed set
    intro h
    rcases h with ⟨hn1, hn2⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn1l, hn1u⟩
    interval_cases n <;> try { contradiction } <;> try { native_decide }
  · -- Backward direction: given n is in the right-hand side set, prove n in range 1 ≤ n ≤ 100 and Odd (n.divisors.card)
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · -- n = 1
      constructor
      · -- Show that 1 ∈ [1, 100]
        native_decide
      · -- Show that Odd (Nat.divisors 1).card
        native_decide
    · -- n = 4
      constructor
      · -- Show that 4 ∈ [1, 100]
        native_decide
      · -- Show that Odd (Nat.divisors 4).card
        native_decide
    · -- n = 9
      constructor
      · -- Show that 9 ∈ [1, 100]
        native_decide
      · -- Show that Odd (Nat.divisors 9).card
        native_decide
    · -- n = 16
      constructor
      · -- Show that 16 ∈ [1, 100]
        native_decide
      · -- Show that Odd (Nat.divisors 16).card
        native_decide
    · -- n = 25
      constructor
      · -- Show that 25 ∈ [1, 100]
        native_decide
      · -- Show that Odd (Nat.divisors 25).card
        native_decide
    · -- n = 36
      constructor
      · -- Show that 36 ∈ [1, 100]
        native_decide
      · -- Show that Odd (Nat.divisors 36).card
        native_decide
    · -- n = 49
      constructor
      · -- Show that 49 ∈ [1, 100]
        native_decide
      · -- Show that Odd (Nat.divisors 49).card
        native_decide
    · -- n = 64
      constructor
      · -- Show that 64 ∈ [1, 100]
        native_decide
      · -- Show that Odd (Nat.divisors 64).card
        native_decide
    · -- n = 81
      constructor
      · -- Show that 81 ∈ [1, 100]
        native_decide
      · -- Show that Odd (Nat.divisors 81).card
        native_decide
    · -- n = 100
      constructor
      · -- Show that 100 ∈ [1, 100]
        native_decide
      · -- Show that Odd (Nat.divisors 100).card
        native_decide