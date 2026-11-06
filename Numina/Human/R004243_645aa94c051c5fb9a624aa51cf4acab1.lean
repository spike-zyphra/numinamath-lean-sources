import Mathlib

/- 7. (1) Does there exist a cube that can be expressed as the sum of two squares?
(2) Does there exist a fourth power that can be expressed as the sum of two squares? -/
theorem number_theory_244585 :
    (∃ n : ℕ, ∃ a b : ℕ, n^3 = a^2 + b^2) ∧
    (∃ m : ℕ, ∃ c d : ℕ, m^4 = c^2 + d^2) := by
      constructor
      --Observe that 10^2 + 5^2 = 5^3
      use 5, 10, 5
      norm_num
      --Observe that 15^2 + 20^2 = 5^4
      use 5, 15, 20
      norm_num