import Mathlib

/-Let $M$ be a positive integer. Determine all natural numbers $b$ for which the equality $11_b \cdot 22_b \cdot
MM_b = 13310_b$ holds in the number system with base $b$. (This means that $M$ must be less than $b$,
and all other digits appearing in the numbers must also be less than $b$.) Show that if $M \geq 2$,
the unique solution is $b=2M$. If $M=1$, show there is no solution.
-/

theorem number_theory_639727 (M: ℤ):
  (2 ≤ M → {b: ℤ | M < b ∧ 3 < b ∧ (b + 1) * (2 * b + 2) * (M * b + M) = b ^ 4 + 3 * b ^ 3 + 3 * b ^ 2 + b} = {2 * M}) ∧
  (M = 1 → {b: ℤ | M < b ∧ 3 < b ∧ (b + 1) * (2 * b + 2) * (M * b + M) = b ^ 4 + 3 * b ^ 3 + 3 * b ^ 2 + b} = ∅) := by

  constructor

  -- the case M ≥ 2
  .
    intro hm
    ext b
    constructor

    -- the forward direction
    .
      intro h
      simp at h
      rcases h with ⟨l1, l2, h⟩
      simp
      rw [show (b + 1) * (2 * b + 2) * (M * b + M) = 2 * M * (b + 1) ^ 3 by ring] at h
      rw [show b ^ 4 + 3 * b ^ 3 + 3 * b ^ 2 + b = b * (b + 1) ^ 3 by ring] at h
      replace h: (2 * M - b) * (b + 1) ^ 3 = 0 := by
        nlinarith
      simp at h
      rcases h with h | h
      .
        omega
      .
        omega

    -- the backward direction
    .
      intro h
      simp at h
      simp [h]
      refine ⟨by omega, by omega, ?_⟩
      ring


  -- the case M = 1
  .
    intro hm
    simp [hm]
    ext b
    constructor

    -- the forward direction
    .
      intro h
      simp at h
      simp
      rcases h with ⟨l1, l2, h⟩
      rw [show (b + 1) * (2 * b + 2) * (b + 1) = 2 * (b + 1) ^ 3 by ring] at h
      rw [show b ^ 4 + 3 * b ^ 3 + 3 * b ^ 2 + b = b * (b + 1) ^ 3 by ring] at h
      replace h: (2 - b) * (b + 1) ^ 3 = 0 := by
        nlinarith
      simp at h
      omega

    -- the backward direction
    .
      intro h
      tauto
