import Mathlib

theorem number_theory_26928 (n : ℤ) :
    ∃ x y z : ℤ, x^3 + 2 * y^2 + 4 * z = n := by
  by_cases h1 : n % 4 = 0
  · -- Assume n ≡ 0 (mod 4).
    have h2 : ∃ m, n = 4 * m := by 
      refine' ⟨n / 4, by omega⟩
    rcases h2 with ⟨m, hm⟩
    use 0
    use 0
    use m
    rw [hm]
    all_goals ring
  by_cases h2 : n % 4 = 2
  · -- Assume n ≡ 2 (mod 4).
    have h3 : ∃ m, n = 4 * m + 2 := by 
      refine' ⟨(n - 2) / 4, by omega⟩
    rcases h3 with ⟨m, hm⟩
    use 0
    use 1
    use m
    rw [hm]
    all_goals ring
  by_cases h3 : n % 2 = 1
  · -- Assume n is odd.
    have h4 : ∃ k, n = 2 * k + 1 := by 
      refine' ⟨(n - 1) / 2, by omega⟩
    rcases h4 with ⟨k, hk⟩
    by_cases h4k : k % 2 = 0
    · -- Assume k is even.
      have h5 : ∃ m, k = 2 * m := by 
        refine' ⟨k / 2, by omega⟩
      rcases h5 with ⟨m, hm⟩
      use 1
      use 0
      use m
      rw [hk, hm]
      all_goals ring
    · -- Assume k is odd.
      have h6 : ∃ m, k = 2 * m + 1 := by 
        refine' ⟨(k - 1) / 2, by omega⟩
      rcases h6 with ⟨m, hm⟩
      use 1
      use 1
      use m
      rw [hk, hm]
      all_goals ring
  omega