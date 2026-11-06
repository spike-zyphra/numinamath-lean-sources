import Mathlib

/-Alex has 12 friends and 63 coins.
What is the minimum number of additional coins he needs so that
he can give each friend at least one coin and no two friends receive the same number of coins?-/

-- define the possible coins distribution function for total 78 coins
def x: ℕ → ℕ := fun n => n + 1

theorem algebra_14234: IsLeast {n: ℕ | ∃ a: ℕ → ℕ, 0 < a 0 ∧ (∀ i j, i < j → j < 12 → a i < a j) ∧
  ∑ i ∈ Finset.range 12, a i = (n + 63)} 15 := by

  constructor

  -- the forward direction
  .
    simp
    use x
    simp [x]
    norm_num
    intro i j h1 h2
    omega

  -- the reverse direction
  .
    intro n h
    simp at h
    obtain ⟨a, ha0, ha1, ha2⟩ := h

    -- we prove i + 1 ≤ a i by induction
    have hi: ∀ i, i < 12 → i + 1 ≤ a i := by
      intro i hi
      induction' i with i ih
      .
        omega
      .
        have s: i < 12 := by omega
        simp [hi] at ih
        have u: a i + 1 ≤ a (i + 1) := by
          specialize ha1 i (i + 1) (by omega) (by omega)
          omega
        omega

    suffices 78 ≤ n + 63 by omega
    rw [← ha2]
    have r: ∑ i ∈ Finset.range 12, (i + 1) ≤ ∑ i ∈ Finset.range 12, a i := by
      apply Finset.sum_le_sum
      intro i t
      simp at t
      specialize hi i (by omega)
      exact hi
    have r1: ∑ i ∈ Finset.range 12, (i + 1) = 78 := by
      simp [Finset.sum_range_succ]
    rw [r1] at r
    linarith