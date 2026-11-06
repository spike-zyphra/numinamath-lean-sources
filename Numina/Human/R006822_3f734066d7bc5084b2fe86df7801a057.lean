import Mathlib

/- Let $n$ be a positive four-digit integer.
Suppose $n$ is equal to the fifth power of its unit digit (the unit digit is taken in base 10).
Find all such $n$.
Show that $n \in \{1024, 3125, 7776\}$.-/

theorem number_theory_641472: {n: ℕ | n ∈ Finset.Icc 1000 9999 ∧ n = (n % 10) ^ 5}
  = {1024,3125,7776} := by

  ext n
  constructor

  -- the forward direction
  .
    intro h
    simp at h
    simp
    rcases h with ⟨h1, h2⟩
    set a:= n % 10
    have ha: a < 10 := by omega

    -- we show that 4 ≤ a
    have u: 4 ≤ a := by
      by_contra! o
      interval_cases a
      .
        simp at h2
        simp [h2] at h1
      .
        simp at h2
        simp [h2] at h1
      .
        simp at h2
        simp [h2] at h1
      .
        simp at h2
        simp [h2] at h1

    -- we show that a ≤ 6
    have v: a < 7 := by
      by_contra! v
      have s: 7 ^ 5 ≤ n := by
        rw [h2]
        apply Nat.pow_le_pow_left
        omega
      rcases h1 with ⟨l1, l2⟩
      absurd l2
      simp
      simp at s
      omega

    interval_cases a
    all_goals simp [h2]


  -- the backward direction
  .
    intro h
    simp at h
    rcases h with rfl | rfl | rfl
    all_goals simp

