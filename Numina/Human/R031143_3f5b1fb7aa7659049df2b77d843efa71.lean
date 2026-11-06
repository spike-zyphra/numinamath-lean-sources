import Mathlib

open Real

/- Exercise 4. Let $n$ be a strictly positive integer and $x \geqslant n$ a real number. Show that $x+\frac{n}{x} \geqslant n+1$ and determine the cases of equality. -/
theorem inequalities_292914 (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : n ≤ x) :
    x + n / x ≥ n + 1 ∧ (x + n / x = n + 1 ↔ x = n) := by
  -- First, we show that the difference between the left and right sides is non-negative
  have h1 : x + n / x - (n + 1) ≥ 0 := by
    -- We need to establish that x > 0 for division to be valid
    have h2 : x > 0 := by
      have h3 : (n : ℝ) > 0 := by exact_mod_cast hn
      linarith
    -- Rewrite the difference in a form that makes it easier to prove non-negativity
    have h4 : x + n / x - (n + 1) = (x - n) * (x - 1) / x := by
      field_simp
      ring_nf
    rw [h4]
    -- Show that the numerator (x - n) * (x - 1) is non-negative
    have h5 : (x - n) * (x - 1) ≥ 0 := by
      apply mul_nonneg
      · -- Show x - n ≥ 0
        linarith [hx]
      · -- Show x - 1 ≥ 0
        have h6 : (n : ℝ) ≥ 1 := by
          have h7 : n ≥ 1 := by linarith
          exact_mod_cast h7
        nlinarith
    -- Show that the entire fraction is non-negative
    have h7 : (x - n) * (x - 1) / x ≥ 0 := by
      apply div_nonneg
      · exact h5
      · -- Show x ≥ 0 (but actually x > 0)
        linarith
    linarith
  -- Construct the conjunction for our theorem
  constructor
  · linarith
  · constructor
    · -- First direction: Assume x + n/x = n + 1, prove x = n
      intro h
      have h2 : x + n / x - (n + 1) = 0 := by linarith
      -- Show that (x - n) * (x - 1) = 0, which means either x = n or x = 1
      have h3 : (x - n) * (x - 1) = 0 := by
        have h4 : x ≠ 0 := by
          have h5 : (n : ℝ) > 0 := by exact_mod_cast hn
          linarith
        have h5 : (x - n) * (x - 1) / x = 0 := by
          have h6 : x + n / x - (n + 1) = (x - n) * (x - 1) / x := by
            field_simp
            ring_nf
          rw [h6] at h2
          linarith
        have h6 : (x - n) * (x - 1) = 0 := by
          have h8 : (x - n) * (x - 1) = 0 := by
            have h9 : (x - n) * (x - 1) / x = 0 := by linarith
            have h10 : x ≠ 0 := h4
            field_simp at h9 ⊢
            linarith
          linarith
        linarith
      -- Apply the zero product property to handle both cases
      cases' (mul_eq_zero.mp h3) with h7 h8
      · -- Case x - n = 0
        linarith
      · -- Case x - 1 = 0
        have h9 : x = 1 := by linarith
        -- If x = 1, then n must also be 1 (since n ≤ x and n ≥ 1)
        have h10 : (n : ℝ) = 1 := by
          have h13 : (n : ℝ) ≥ 1 := by
            have h14 : n ≥ 1 := by linarith
            exact_mod_cast h14
          linarith
        -- Conclude that x = n
        have h11 : (x : ℝ) = (n : ℝ) := by
          rw [h9, h10]
        exact_mod_cast h11
    · -- Second direction: Assume x = n, prove x + n/x = n + 1
      intro h
      rw [h]
      -- Establish that n > 0 and n ≠ 0 for division
      have h2 : (n : ℝ) > 0 := by exact_mod_cast hn
      have h3 : (n : ℝ) ≠ 0 := by linarith
      field_simp
