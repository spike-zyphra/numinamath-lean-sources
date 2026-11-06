import Mathlib

theorem number_theory_93594 :
    Finset.card
      { (a, b, c) : (Finset.Icc 1 100) × (Finset.Icc 1 100) × (Finset.Icc 1 100) |
        a.1 ∣ b.1 ∧ a.1 ∣ c.1 ∧ a.1 + b.1 + c.1 = 100 } = 200 := by
  native_decide