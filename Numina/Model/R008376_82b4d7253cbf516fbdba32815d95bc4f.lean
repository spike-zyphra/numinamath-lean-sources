import Mathlib

theorem number_theory_131848 :
    (Nat.factorization (2^27 + 1) 3) = 4 ∧
    (Nat.factorization (161^14 - 112^14) 7) = 16 ∧
    (Nat.factorization (7^20 + 1) 2) = 1 ∧
    (Nat.factorization (17^48 - 5^48) 2) = 6 := by native_decide