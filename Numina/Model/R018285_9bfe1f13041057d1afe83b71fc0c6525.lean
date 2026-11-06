import Mathlib

theorem number_theory_300015 :
    {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ ∃ k, k^2 = 23 * x + 92 * y ∧ k^2 ≤ 2392}.ncard = 27 := by
  have h1 : {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ ∃ k, k^2 = 23 * x + 92 * y ∧ k^2 ≤ 2392} = Finset.filter (fun p : ℕ × ℕ => p.1 > 0 ∧ p.2 > 0 ∧ (23 * p.1 + 92 * p.2 : ℕ) ≤ 2392 ∧ IsSquare (23 * p.1 + 92 * p.2 : ℕ)) (Finset.Icc (0 : ℕ) 103 ×ˢ Finset.Icc (0 : ℕ) 26) := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Assume h
      rintro ⟨hx, hy, k, hk1, hk2⟩
      have h2 : k ≤ 48 := by nlinarith
      have h8 : x ≤ 103 := by
        nlinarith [sq_nonneg (k : ℕ), hk1, hk2]
      have h9 : y ≤ 26 := by
        nlinarith [sq_nonneg (k : ℕ), hk1, hk2]
      refine ⟨⟨by omega, by omega⟩, hx, hy, by omega, by
        have h3 : IsSquare (23 * x + 92 * y : ℕ) := by
          use k
          all_goals
            ring_nf at hk1 ⊢
            all_goals
              omega 
        exact h3
      ⟩
    · -- Assume h
      rintro ⟨⟨hx1, hy1⟩, hx, hy, hk2, hk⟩
      constructor
      · exact hx
      constructor
      · exact hy
      · -- Show existence of k 
        rcases hk with ⟨k, hk1⟩
        refine ⟨k, by linarith, by linarith⟩
  rw [h1] 
  rw [Set.ncard_coe_Finset] 
  native_decide