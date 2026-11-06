import Mathlib

/-Find infinitely many different sets of positive integers x,y,z, such that
x^1+1=y^2+z^2, and the last several digits of z^2 are the same as those of x^2+1-/
theorem number_theory_177308 :
    ∀ n : ℕ, ∃ x y z : ℕ,
      x > 0 ∧ y > n ∧ z > 0 ∧
      x^2 + 1 = y^2 + z^2 ∧
      (z^2) % 1000 = (x^2 + 1) % 1000 := by
  intro n
  by_cases l: n = 0
  -- case n = 0
  . use 100
    use 100
    use 1
    omega
  -- case n > 0, let u = 1000n, y = u ^ 3,x = u^3 + 2u, z = 2u^2+1
  . replace l: 1 ≤ n := by omega
    set u := 1000 * n with hu
    use (u ^ 3 + 2 * u)
    use (u ^ 3)
    use (2 * u ^ 2 + 1)
    constructor
    . omega
    . constructor
      . simp [u]
        calc
          n < 1000 * n := by omega
          _ ≤ (1000 * n) ^ 3 := by nth_rewrite 1[show 1000 * n = (1000 * n) ^ 1 by ring]; apply Nat.pow_le_pow_of_le_right; omega;omega
      . constructor
        . omega
        . constructor
          . zify
            ring
          . ring_nf
            omega
            