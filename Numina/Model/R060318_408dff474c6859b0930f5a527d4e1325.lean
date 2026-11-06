import Mathlib

theorem number_theory_7752 :
    ∀ N : ℕ, ∃ n : ℤ, n > N ∧
      ∃ a b : ℤ, n = a^2 + b^2 ∧
      ∃ c d : ℤ, n + 1 = c^2 + d^2 ∧
      ∃ e f : ℤ, n + 2 = e^2 + f^2 := by
  intro N
  use 4 * ((N : ℤ) + 1)^4 + 4 * ((N : ℤ) + 1)^2
  constructor
  · -- Show that our number is greater than N
    nlinarith
  · -- Show expression for n, n+1, n+2 as sums of two squares
    use 2 * ((N + 1 : ℤ)^2)
    use 2 * ((N + 1 : ℤ))
    constructor
    · -- Verify n = a^2 + b^2
      ring_nf
    · -- Show expressions for n+1 and n+2
      use 2 * ((N + 1 : ℤ)^2) + 1
      use 0
      constructor
      · -- Verify n + 1 = c^2 + d^2
        ring_nf
      · -- Show expression for n+2
        use 2 * ((N + 1 : ℤ)^2) + 1
        use 1
        · -- Verify n + 2 = e^2 + f^2
          ring_nf