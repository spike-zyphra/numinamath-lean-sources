import Mathlib

/- Let $a, b, c$ be not necessarily distinct integers between 1 and 2011, inclusive. Find the smallest possible value of $\frac{a b+c}{a+b+c}$.-/
theorem algebra_608910 :
    IsLeast {q : ℚ | ∃ a b c : ℤ, a ∈ Set.Icc 1 2011 ∧ b ∈ Set.Icc 1 2011 ∧ c ∈ Set.Icc 1 2011 ∧ q = (a * b + c : ℚ) / (a + b + c)} (2 / 3 : ℚ) := by
  -- Break the goal into two parts.
  simp [IsLeast, lowerBounds]
  refine ⟨?_, ?_⟩
  . -- First show that 2 / 3 is indeed possible.
    use 1, by norm_num, 1, by norm_num, 1, by norm_num, by norm_num
  . -- Then show that 2 / 3 is a lower bound.
    intro q a ha₀ ha₁ b hb₀ hb₁ c hc₀ hc₁ hq
    rw [hq]
    -- Show that (ab + c) / (a + b + c) < 1 ↔ (a = 1 ∨ b = 1)
    have h₀ : (a * b + c : ℚ) / (a + b + c) < 1 ↔ (a = 1 ∨ b = 1) := by
      calc
        (a * b + c : ℚ) / (a + b + c) < 1
        _ ↔ (a * b - a - b : ℚ) / (a + b + c) < 0 := by
          -- Note that (ab + c) / (a + b + c) = (ab - a - b) / (a + b + c) + 1.
          rw [show (a * b + c : ℚ) = (a * b - a - b + (a + b + c)) by ring, add_div, div_self (by norm_cast; linarith)]
          apply Iff.intro
          all_goals
            intro _
            linarith
        _ ↔ (a * b - a - b : ℚ) < 0 := by
          -- Show that (ab - a - b) / (a + b + c) < 0 ↔ ab - a - b < 0.
          rw [div_lt_iff₀]
          simp
          by_contra!
          norm_cast at this
          linarith
        _ ↔ (a - 1) * (b - 1) < 1 := by
          qify
          apply Iff.intro
          all_goals
            intro _
            linarith
        _ ↔ (a - 1) * (b - 1) = 0 := by
          have : (a - 1) * (b - 1) ≥ 0 := by nlinarith
          omega
        _ ↔ (a = 1 ∨ b = 1) := by
          simp [sub_eq_zero]
    by_cases h₁ : (a * b + c : ℚ) / (a + b + c) < 1
    . -- If (ab + c) / (a + b + c) < 1, then a = 1 or b = 1.
      rw [h₀] at h₁
      cases h₁ with
      | inl h₁ =>
        -- If a = 1, then (ab + c) / (a + b + c) is minimized when b = c = 1.
        simp [h₁]
        calc
          (2 / 3 : ℚ) = 1 - 1 / 3 := by norm_num
          _ ≤ 1 - 1 / (1 + b + c : ℚ) := by
            apply sub_le_sub_left
            apply one_div_le_one_div_of_le
            norm_num
            norm_cast
            linarith
          _ = (b + c : ℚ) / (1 + b + c) := by
            field_simp
            ring
      | inr h₁ =>
        -- If b = 1, then (ab + c) / (a + b + c) is minimized when a = c = 1.
        simp [h₁]
        calc
          (2 / 3 : ℚ) = 1 - 1 / 3 := by norm_num
          _ ≤ 1 - 1 / (a + 1 + c : ℚ) := by
            apply sub_le_sub_left
            apply one_div_le_one_div_of_le
            norm_num
            norm_cast
            linarith
          _ = (a + c : ℚ) / (a + 1 + c) := by
            field_simp
            ring
    . -- If (ab + c) / (a + b + c) ≥ 1, then the result is obvious.
      linarith
