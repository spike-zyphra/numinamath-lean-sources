import Mathlib

theorem algebra_167554 (a : ℕ → ℝ) (h1 : a 1 = 1) (h : ∀ m n, m ≥ n → a (m + n) + a (m - n)
    = (a (2 * m) + a (2 * n)) / 2) : a 2020 = 2020 ^ 2 := by
  have h0 : a 0 = (0 : ℝ) := by
    have h11 := h 0 0 (by omega)
    simp at h11
    linarith

  have h2 : ∀ m : ℕ, a (2 * m) = 4 * a m := by
    intro m
    have h11 := h m 0 (by omega)
    simp at h11
    linarith

  -- Calculate a_2
  have h_a2 : a 2 = (4 : ℝ) := by
    have h' := h 1 0 (by omega)
    norm_num [h1, h0] at h'
    linarith

  -- Now prove a_n = n^2 by induction
  have h3 : ∀ k : ℕ, a k = (↑k : ℝ) ^ 2 := by
    intro k
    induction' k using Nat.strongRecOn with k ih
    cases k with
    | zero =>
      simp [h0]
    | succ k =>
      cases k with
      | zero =>
        simp [h1]
        all_goals try linarith
      | succ k =>
        -- Now we need to compute a_{k+2}
        have h12 := h (k + 1) 1 (by omega)
        simp at h12
        have hk1 := ih (k + 1) (by omega)
        have hk0 := ih k (by omega)
        specialize h2 (k + 1)
        simp [show (k + 1 + 1 : ℕ) = k + 2 by omega, h_a2] at h12 ⊢
        simp [h2, hk1, hk0] at h12 ⊢
        ring_nf at h12 ⊢
        all_goals
          try nlinarith [hk1, hk0, h_a2, h2]
        all_goals
          try ring_nf at h12 ⊢
          <;> nlinarith [hk1, hk0, h_a2]

  -- Final answer
  specialize h3 2020
  norm_num at h3 ⊢
  linarith