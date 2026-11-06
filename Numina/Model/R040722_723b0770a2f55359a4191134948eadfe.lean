import Mathlib

theorem number_theory_173804 :
    (∃ x y z w : ℤ, x^3 + y^3 + z^3 + w^3 = 6) ∧
    (∃ x y z w : ℤ, x^3 + y^3 + z^3 + w^3 = -6) ∧
    (∃ x y z w : ℤ, x^3 + y^3 + z^3 + w^3 = 12) ∧
    (∃ x y z w : ℤ, x^3 + y^3 + z^3 + w^3 = -12) ∧
    (∃ x y z w : ℤ, x^3 + y^3 + z^3 + w^3 = 18) ∧
    (∃ x y z w : ℤ, x^3 + y^3 + z^3 + w^3 = -18) ∧
    (∃ x y z w : ℤ, x^3 + y^3 + z^3 + w^3 = 24) ∧
    (∃ x y z w : ℤ, x^3 + y^3 + z^3 + w^3 = -24) ∧
    (∀ n : ℤ, 6 ∣ n → ∃ x y z w : ℤ, x^3 + y^3 + z^3 + w^3 = n) := by
  constructor
  · -- We will express 6 as the sum of four integer cubes.
    exact ⟨2, 0, -1, -1, by norm_num⟩
  constructor
  · -- We will express -6 as the sum of four integer cubes.
    exact ⟨-2, 0, 1, 1, by norm_num⟩
  constructor
  · -- We will express 12 as the sum of four integer cubes.
    exact ⟨3, 1, -2, -2, by norm_num⟩
  constructor
  · -- We will express -12 as the sum of four integer cubes.
    exact ⟨-3, -1, 2, 2, by norm_num⟩
  constructor
  · -- We will express 18 as the sum of four integer cubes.
    exact ⟨4, 2, -3, -3, by norm_num⟩
  constructor
  · -- We will express -18 as the sum of four integer cubes.
    exact ⟨-4, -2, 3, 3, by norm_num⟩
  constructor
  · -- We will express 24 as the sum of four integer cubes.
    exact ⟨5, 3, -4, -4, by norm_num⟩
  constructor
  · -- We will express -24 as the sum of four integer cubes.
    exact ⟨-5, -3, 4, 4, by norm_num⟩
  · -- We will show that every integer multiple of 6 can be expressed as the sum of four integer cubes.
    intro n hn
    have h1 : ∃ k : ℤ, n = 6 * k := by
      refine' ⟨n / 6, by omega⟩
    rcases h1 with ⟨k, hk⟩
    refine' ⟨k + 1, k - 1, -k, -k, by
      rw [hk]
      ring_nf⟩