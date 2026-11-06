import Mathlib


theorem number_theory_119556 (a b : ℤ) (ha : 5 * a ≥ 7 * b) (hb : 7 * b ≥ 0) :
    ∃ x y z u : ℕ, x + 2 * y + 3 * z + 7 * u = a ∧ y + 2 * z + 5 * u = b := by

  have h1 : b ≥ 0 := by
    omega

  have h3 : ∃ z u : ℤ, z ≥ 0 ∧ u ≥ 0 ∧ a - 2 * b + z + 3 * u ≥ 0 ∧ b - 2 * z - 5 * u ≥ 0 := by
    by_cases h4 : 2 * b - a ≤ 0
    ·
      use 0
      use (b / 5)
      constructor
      ·
        omega
      constructor
      ·
        omega
      constructor
      ·
        omega
      ·
        omega
    ·
      have h5 : 2 * b - a > 0 := by omega
      have h6 : (2 * b - a) % 3 = 0 ∨ (2 * b - a) % 3 = 1 ∨ (2 * b - a) % 3 = 2 := by
        omega
      rcases h6 with (h6 | h6 | h6)
      ·
        have h7 : ∃ k : ℤ, 2 * b - a = 3 * k := by
          refine' ⟨(2 * b - a) / 3, by omega⟩
        rcases h7 with ⟨k, hk⟩
        use 0
        use k
        constructor
        ·
          omega
        constructor
        ·
          omega
        constructor
        ·
          omega
        ·
          omega
      ·
        have h7 : ∃ k : ℤ, 2 * b - a = 3 * k + 1 := by
          refine' ⟨(2 * b - a - 1) / 3, by omega⟩
        rcases h7 with  ⟨k, hk⟩
        use 1
        use k
        constructor
        ·
          omega
        constructor
        ·
          omega
        constructor
        ·
          omega
        ·
          omega
      ·
        have h7 : ∃ k : ℤ, 2 * b - a = 3 * k + 2 := by
          refine' ⟨(2 * b - a - 2) / 3, by omega⟩
        rcases h7 with  ⟨k, hk⟩
        use 2
        use k
        constructor
        ·
          omega
        constructor
        ·
          omega
        constructor
        ·
          omega
        ·
          omega

  rcases h3 with ⟨z, u, hz, hu, h31, h32⟩

  have h4 : a - 2 * b + z + 3 * u ≥ 0 := by linarith
  have h5 : b - 2 * z - 5 * u ≥ 0 := by linarith

  use (a - 2 * b + z + 3 * u).toNat, (b - 2 * z - 5 * u).toNat, z.toNat, u.toNat
  constructor
  ·
    omega
  ·
    omega