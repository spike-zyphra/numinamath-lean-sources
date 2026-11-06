import Mathlib

theorem algebra_197199 (f : ℝ → ℝ)
    (h₀ : ∀ x, x < 1 → f x = -2 * x + 1)
    (h₁ : ∀ x, x ≥ 1 → f x = x ^ 2 - 2 * x) :
    IsGreatest {x | ∃ n : ℤ, f x = 3 ∧ x = n} 3 := by
  constructor
  · -- Show 3 is in the set
    use 3
    norm_num
    all_goals
      norm_num [h₁]
      all_goals norm_num
  · -- Show that 3 is greatest in the set
    intro y hy
    rcases hy with ⟨n, hn1, hn2⟩
    have h3 : (y : ℝ) = (n : ℝ) := by linarith [hn2]
    rw [show f y = f (n : ℝ) by rw [h3]] at hn1
    by_cases h4 : (n : ℝ) < (1 : ℝ)
    · -- Case n < 1
      have hn4 : f (n : ℝ) = 3 := hn1
      have h5 : f (n : ℝ) = -2 * (n : ℝ) + 1 := h₀ (n : ℝ) h4
      rw [h5] at hn4
      have h6 : (n : ℝ) = (-1 : ℝ) := by linarith
      have h7 : n = -1 := by
        exact_mod_cast h6
      have h8 : (n : ℝ) ≤ (3 : ℝ) := by
        have h9 : (n : ℝ) = (-1 : ℝ) := h6
        linarith
      linarith [h3, h8]
    · -- Case n ≥ 1
      have hn8 : (n : ℝ) ≥ (1 : ℝ) := by linarith
      have h9 : f (n : ℝ) = 3 := hn1
      have h10 : f (n : ℝ) = (n : ℝ) ^ 2 - 2 * (n : ℝ) := h₁ (n : ℝ) (by linarith)
      rw [h10] at h9
      have h11 : (n : ℝ) ^ 2 - 2 * (n : ℝ) - 3 = (0 : ℝ) := by linarith
      have h12 : ((n : ℝ) - (3 : ℝ)) * ((n : ℝ) + (1 : ℝ)) = (0 : ℝ) := by
        ring_nf at h11 ⊢
        linarith
      cases' (mul_eq_zero.1 h12) with h13 h14
      · -- Case n = 3
        have h15 : (n : ℝ) = (3 : ℝ) := by linarith
        have h16 : n = 3 := by
          exact_mod_cast h15
        have h17 : (n : ℝ) ≤ (3 : ℝ) := by
          have h18 : (n : ℝ) = (3 : ℝ) := h15
          linarith
        linarith [h3, h17]
      · -- Case n = -1, contradiction with n ≥ 1
        have h18 : (n : ℝ) = (-1 : ℝ) := by linarith
        linarith [show (n : ℝ) ≥ (1 : ℝ) from hn8, h18]