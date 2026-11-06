import Mathlib

theorem number_theory_244914 :
    (2^100 + 3^100 : ℕ) < 4^100 ∧
    ∃ x y, 2^x * 3^y = (∏ i ∈ Finset.range 60, (24^(1 / (i + 1)) : ℕ)^i) := by
  constructor
  · -- Show $2^{100} + 3^{100} < 4^{100}$.
    norm_num
  · -- Show exists natural numbers x and y such that the equation.
    use 0, 0
    native_decide