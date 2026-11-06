import Mathlib

theorem algebra_283266 {a b c : ℕ} (h₀ : a * b = 24) (h₁ : b * c = 32) (h₂ : a * c = 48) :
    a = 6 ∧ b = 4 ∧ c = 8 := by
  have h3 : (a * b * c) ^ 2 = 36864 := by 
    calc
      (a * b * c) ^ 2 = (a * b) * (b * c) * (a * c) := by 
        ring
      _ = 24 * 32 * 48 := by 
        rw [h₀, h₁, h₂]
      _ = 36864 := by 
        norm_num
  -- From the squared value compute the base value
  have h4 : a * b * c = 192 := by
    nlinarith
  -- From h2: a * c = 48 and h4: a * b * c = 192. Thus b = 4
  have h5 : b = 4 := by
    have eq1 : a * b * c = 192 := h4
    have eq2 : a * c = 48 := h₂
    -- From eq1: a * b * c = 192
    -- From eq2: a * c = 48.
    -- Substitute eq2 into eq1: b * (a * c) = b * 48 = 192
    -- Then, b = 192 / 48 = 4
    have h6 : b = 4 := by
      nlinarith [eq1, eq2]
    exact h6 
  -- Now with b = 4, and from h0 a * 4 = 24 => a = 6
  have h4a : a = 6 := by 
    nlinarith [h5, h₀]
  -- Now with b = 4, and from h1 4 * c = 32 => c = 8
  have h4c : c = 8 := by 
    nlinarith [h5, h₁]
  exact ⟨h4a, h5, h4c⟩