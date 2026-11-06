import Mathlib

theorem algebra_170518 (n : ℕ) (hn : n ≥ 2) (M : ℕ × ℕ)
    (hM : M.1 = n * M.2 ^ 2 - 1 ∧ M.2 = M.1) :
    ∀ m > 0, ∃ k ≥ 2, (M.1 ^ m, M.2 ^ m) ∈ {(x, y) | y ^ 2 = k * x - 1 ∧ y = x} := by
  rcases hM with ⟨h1, h2⟩
  have eq1 : M.1 = n * M.1 ^ 2 - 1 := by
    rw [show M.2 = M.1 by omega] at h1
    omega
  by_cases h : M.1 = 0
  · -- Case where $M.1 = 0$.
    intro m hm
    use 2
    constructor
    . -- Show k ≥ 2.
      omega
    . -- Show (M.1 ^ m, M.2 ^ m) in the intersection.
      simp [h, h2]
      have zero_pow : 0 ^ m = 0 := by
        have h_zero_pow : 0 ^ m = 0 := by 
          have m1 : m > 0 := hm
          have m2 : m ≠ 0 := by omega
          simp [Nat.zero_pow]
          all_goals omega
        linarith
      simp [zero_pow] at *
      all_goals omega
  · -- Case where $M.1 ≠ 0$.
    have h9 : M.1 ≥ 1 := by 
      omega
    have eq1' : n * M.1 ^ 2 = M.1 + 1 := by
      have eq7 : M.1 = n * M.1 ^ 2 - 1 := eq1
      omega
    intro m hm
    have h7 : M.1 = 1 := by
      have h9 : M.1 ≥ 1 := h9
      nlinarith [sq_nonneg (M.1 * n : ℕ), sq_nonneg ((M.1) : ℕ), sq_nonneg ((n) : ℕ), sq_nonneg ((M.1 -1: ℕ): ℕ), sq_nonneg ((n * (M.1) ) : ℕ)]
    use 2
    constructor
    . -- Show k ≥ 2.
      omega
    . -- Show (M.1 ^ m, M.2 ^ m) in the intersection.
      simp [h2, h7]
      <;> omega