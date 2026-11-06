import Mathlib

theorem inequalities_215698 (a : ℕ → ℝ) (h₀ : a 0 = 0) (h₁ : ∀ n, 0 ≤ a n)
    (h₂ : ∀ i, (a (i - 1) + a (i + 1)) / 2 ≤ a i) :
    ∀ n, 0 < n → (∑ k in Finset.Icc 1 n, a k) ^ 2 ≥
      (3 * (n - 1) / 4) * ∑ k in Finset.Icc 1 n, (a k) ^ 2 := by
  have h3 : a 1 = 0 := by
    have h4 : (a (0 - 1) + a (0 + 1)) / 2 ≤ a 0 := h₂ 0
    norm_num at h4
    rw [h₀] at h4
    have h5 : a 1 ≤ 0 := by linarith
    have h6 : 0 ≤ a 1 := h₁ 1
    linarith
  have h7 : a 2 = 0 := by
    have h8 : (a (1 - 1) + a (1 + 1)) / 2 ≤ a 1 := h₂ 1
    norm_num at h8
    rw [h₀, h3] at h8
    have h9 : a 2 ≤ 0 := by linarith
    have h10 : 0 ≤ a 2 := h₁ 2
    linarith
  have h11 : a 3 = 0 := by
    have h12 : (a (2 - 1) + a (2 + 1)) / 2 ≤ a 2 := h₂ 2
    norm_num at h12
    rw [h3, h7] at h12
    have h13 : a 3 ≤ 0 := by linarith
    have h14 : 0 ≤ a 3 := h₁ 3
    linarith
  -- We need to show that all a_n = 0
  have h17 : ∀ k : ℕ, a k = 0 := by
    intro k
    induction' k using Nat.strongRecOn with k ih
    cases k with
    | zero =>
      rw [h₀]
    | succ m =>
      cases m with
      | zero =>
        linarith [h3]
      | succ p =>
        have h18 : a p = 0 := by
          apply ih
          all_goals
            omega
        have h19 : a (p + 1) = 0 := by
          apply ih
          all_goals
            omega
        have h20 : (a ((p + 1) - 1) + a ((p + 1) + 1)) / 2 ≤ a (p + 1) := h₂ (p + 1)
        have eq1 : (p + 1 : ℕ) - 1 = p := by
          omega
        have eq2 : (p + 1 + 1 : ℕ) = p + 2 := by
          omega
        rw [eq1, eq2] at h20
        rw [show a p = 0 by linarith [h18], show a (p + 1) = 0 by linarith [h19]] at h20
        have h21 : a (p + 2) ≤ 0 := by linarith [h20]
        have h22 : 0 ≤ a (p + 2) := h₁ (p + 2)
        linarith
  intro n hn
  have h18 : ∀ k : ℕ, a k = 0 := h17
  have h19 : (∑ k in Finset.Icc 1 n, a k) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have h18_i : a i = 0 := h18 i
    simpa using h18_i
  have h20 : ∑ k in Finset.Icc 1 n, (a k) ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have h18_i : a i = 0 := h18 i
    have h23 : (a i) ^ 2 = 0 := by
      rw [h18_i]
      norm_num
    simpa using h23
  rw [h19, h20]
  all_goals nlinarith