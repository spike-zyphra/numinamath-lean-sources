import Mathlib

theorem number_theory_210701 {N : ℕ} (hN : N = 142857) :
    (Nat.digits 10 N).length = 6 ∧
    (Nat.digits 10 N).toFinset.card = 6 ∧
    ∀ i ∈ Finset.Icc 2 6, (Nat.digits 10 (i * N)).toFinset = (Nat.digits 10 N).toFinset := by
  subst N
  constructor
  · -- Show that the length of the digits is 6
    norm_num
  constructor
  · -- Show that there are 6 different digits
    native_decide
  · -- Show that multiplying by 2,3,4,5,6 gives a permutation of the digits
    intro i hi
    fin_cases hi <;> native_decide