import Mathlib

theorem number_theory_255218 (n : ℤ) :
    ∃ x y z, 3 * (n - 1) ^ 2 + 8 = x ^ 2 + y ^ 2 + z ^ 2 := by
        use (n + 1)
        use (n - 3)
        use (n - 1)
        nlinarith