import Mathlib

/-Given the system of equations in x and y
x^2-y^2=p,
3xy+p(x-y)=p^2
has integer solutions (x,y).
Find the prime number p that satisfies the condition.-/

theorem algebra_320379: {p: ℤ | Prime p ∧ 0 < p ∧
    ∃ x y: ℤ, x ^ 2 - y ^ 2 = p ∧ 3 * x * y + p * (x - y) = p ^ 2} = {3} := by

    ext p
    constructor
    -- the forward direction
    .
      intro h
      simp at h
      rcases h with ⟨hp, lp, h⟩
      obtain ⟨x, y, h1, h2⟩ := h
      replace h1: p = (x + y) * (x - y) := by
        linarith
      have d: p ∣ (x + y) * (x - y) := by
        rw [h1]
      have d1: (x + y) ∣ p := by
        rw [h1]
        simp
      have d2: (x - y) ∣ p := by
        rw [h1]
        simp
      rw [Prime.dvd_mul] at d
      rcases d with d | d

      -- case 1: p =|x + y|
      .
        by_cases i: 0 ≤ x + y

        -- p = x + y
        .
          have ne: x + y ≠ 0 := by
            by_contra! o
            simp [o] at h1
            simp [h1] at lp
          replace i: 0 < x + y := by omega
          have o: p = x + y := by
            apply Int.dvd_antisymm
            all_goals omega
          simp [o] at h1
          replace h1: x - y = 1 := by nlinarith
          simp [h1] at h2
          replace h2: 3 * (4 * x * y) - 4 * p ^ 2 + 4 * p = 0 := by linarith
          rw [show 4 * x * y = (x + y) ^ 2 - (x - y) ^ 2 by ring] at h2
          simp [h1, ← o] at h2
          ring_nf at h2
          rw [show -3 + (p * 4 - p ^ 2) = - (p - 3) * (p - 1) by ring] at h2
          simp at h2
          rcases h2 with h2 | h2
          .
            simp
            linarith
          .
            replace h2: p = 1 := by omega
            simp [h2] at hp

        -- p = -(x + y)
        .
          simp at i
          replace d1: - (x + y) ∣ p := by
            rw [Int.neg_dvd]
            exact d1
          have o: p = -(x + y) := by
            apply Int.dvd_antisymm
            omega
            linarith
            rw [Int.dvd_neg]
            exact d
            exact d1
          simp [o] at h1
          replace h1: x - y = -1 := by nlinarith
          simp [h1] at h2
          replace h2: 3 * (4 * x * y) - 4 * p ^ 2 - 4 * p = 0 := by linarith
          rw [show 4 * x * y = (x + y) ^ 2 - (x - y) ^ 2 by ring] at h2
          replace o: -p = x + y := by
            simp [o]
          simp [h1, ← o] at h2
          ring_nf at h2
          rw [show -3 + (-(p * 4) - p ^ 2) = - (p + 3) * (p + 1) by ring] at h2
          simp at h2
          rcases h2 with h2 | h2
          .
            linarith
          .
            linarith

      -- case 2: p = |x - y|
      .
        by_cases i: 0 ≤ x - y

        -- p = x - y
        .
          have ne: x - y ≠ 0 := by
            by_contra! o
            simp [o] at h1
            simp [h1] at lp
          replace i: 0 < x - y := by omega
          have o: p = x - y := by
            apply Int.dvd_antisymm
            all_goals omega
          simp [o] at h1
          replace h1: x + y = 1 := by nlinarith
          simp [← o] at h2
          replace h2: 3 * (4 * x * y) + 4 * p ^ 2 - 4 * p = 0 := by nlinarith
          rw [show 4 * x * y = (x + y) ^ 2 - (x - y) ^ 2 by ring] at h2
          simp [h1, ← o] at h2
          ring_nf at h2
          rw [show 3 - p * 4 + p ^ 2 = (p - 1) * (p - 3) by ring] at h2
          simp at h2
          rcases h2 with h2 | h2
          .
            replace h2: p = 1 := by omega
            simp [h2] at hp
          .
            replace h2: p = 3 := by omega
            simp [h2]

        -- p = -(x - y)
        .
          simp at i
          replace d2: - (x - y) ∣ p := by
            rw [Int.neg_dvd]
            exact d2
          have o: p = -(x - y) := by
            apply Int.dvd_antisymm
            omega
            linarith
            rw [Int.dvd_neg]
            exact d
            exact d2
          replace o: - p = x - y := by
            simp [o]
          simp [← o] at h1
          replace h1: x + y = -1 := by nlinarith
          simp [← o] at h2
          replace h2: 3 * (4 * x * y) + 4 * p ^ 2 + 4 * p = 0 := by nlinarith
          rw [show 4 * x * y = (x + y) ^ 2 - (x - y) ^ 2 by ring] at h2
          simp [h1, ← o] at h2
          ring_nf at h2
          rw [show 3 + p * 4 + p ^ 2 = (p + 1) * (p + 3) by ring] at h2
          simp at h2
          rcases h2 with h2 | h2
          .
            linarith
          .
            linarith

      exact hp

    -- the backward direction
    .
      intro h
      simp at h
      simp [h]
      norm_num
      use 2
      use 1
      norm_num