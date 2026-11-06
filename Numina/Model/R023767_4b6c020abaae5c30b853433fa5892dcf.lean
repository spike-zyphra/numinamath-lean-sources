import Mathlib

theorem number_theory_607213 (n : ℕ) (hn : 3 ≤ n) :
  ∃ x y : ℤ, 7 * x ^ 2 + y ^ 2 = 2 ^ n := by
  have h1 : n ≥ 3 := hn
  have h11 : n = 3 ∨ n = 4 ∨ n = 5 ∨ n ≥ 6 := by omega
  rcases h11 with h11 | h11 | h11 | h11
  · -- n = 3
    rw [show n = 3 by omega]
    use 1, 1
    all_goals norm_num
  · -- n = 4
    rw [show n = 4 by omega]
    use 1, 3
    all_goals norm_num
  · -- n = 5
    rw [show n = 5 by omega]
    use 1, 5
    all_goals norm_num
  · -- n >= 6
    have h23 : n ≥ 6 := h11
    have h48 : ∃ x y : ℤ, 7 * x ^ 2 + y ^ 2 = 2 ^ n := by
      have h33 : n ≥ 6 := h23
      have h16 : ∃ k, n = k + 6 := by
        refine ⟨n - 6, by omega⟩
      rcases h16 with ⟨k, hk⟩
      rw [hk]
      have h44 : ∀ (k : ℕ), ∃ x y : ℤ, 7 * x ^ 2 + y ^ 2 = 2 ^ (k + 6 : ℕ) := by
        intro k
        induction' k using Nat.strongRecOn with k ih
        cases k with
        | zero =>
          use 2, 6
          all_goals norm_num
        | succ k =>
          cases k with
          | zero =>
            use 1, 11
            all_goals norm_num
          | succ k =>
            have h33 := ih k (by omega)
            rcases h33 with ⟨x, y, h_eq⟩
            use (x * 2 : ℤ), (y * 2 : ℤ)
            ring_nf at h_eq ⊢
            nlinarith
      specialize h44 k
      simpa using h44
    simpa using h48