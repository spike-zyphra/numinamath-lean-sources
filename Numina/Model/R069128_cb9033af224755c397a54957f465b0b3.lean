import Mathlib

theorem number_theory_181415 :
    ∑ a in Finset.Ico 1 100, ∑ b in Finset.Ico 1 100, ∑ c in Finset.Ico 1 100,
      (if (a < b ∧ b < c ∧ Nat.lcm (Nat.lcm a b) c ∣ a + b + c - 1) then a + b + c else 0) = 44 := by
  native_decide