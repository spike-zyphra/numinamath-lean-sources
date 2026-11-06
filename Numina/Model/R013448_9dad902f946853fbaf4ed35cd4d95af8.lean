import Mathlib

def isZuChongzhi (s : Finset ℕ) : Prop :=
  s.card > 0 ∧ ∀ x ∈ s, x > 0 ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (x * y) % (x + y) = 0

theorem number_theory_318840 :
    ∃ s : Finset ℕ, s.card = 4 ∧ isZuChongzhi s := by
  use {420, 840, 1260, 1680}
  constructor
  · -- Show the set has 4 elements
    native_decide
  · -- Show the set is a Zu Chongzhi array
    constructor
    · -- Show the cardinality is larger than 0
      simp
    · -- For any two distinct numbers in the set, the product is divisible by the sum
      native_decide