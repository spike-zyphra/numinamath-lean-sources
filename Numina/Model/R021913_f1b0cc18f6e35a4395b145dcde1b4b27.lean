import Mathlib

theorem algebra_288005 (a b c : ℝ) (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c)
    (h1 : a^3 - 4 * a = 0) (h2 : b^3 - 4 * b = 0) (h3 : c^3 - 4 * c = 0) :
    a * b * c = 0 := by

  have h1' : a * (a^2 - 4) = 0 := by 
    linarith
  have h2' : b * (b^2 - 4) = 0 := by 
    linarith
  have h3' : c * (c^2 - 4) = 0 := by 
    linarith
  have h1a : a = 0 ∨ a^2 = 4 := by 
    cases (mul_eq_zero.mp h1') with
    | inl h => 
      left
      linarith 
    | inr h => 
      right
      linarith
  have h1b : b = 0 ∨ b^2 = 4 := by
    cases (mul_eq_zero.mp h2') with
    | inl h => 
      left
      linarith
    | inr h => 
      right
      linarith
  have h1c : c = 0 ∨ c^2 = 4 := by 
    cases (mul_eq_zero.mp h3') with
    | inl h => 
      left 
      linarith
    | inr h => 
      right
      linarith

  by_cases ha0 : a = 0 
  · -- Assume a = 0
    rw [ha0]
    norm_num
  by_cases hb0 : b = 0 
  · -- Assume b = 0 
    rw [hb0]
    norm_num
  by_cases hc0 : c = 0 
  · -- Assume c = 0 
    rw [hc0]
    norm_num

  have ha2 : a^2 = 4 := by 
    cases h1a with 
    | inl h => 
      contradiction 
    | inr h => 
      linarith 
  have hb2 : b^2 = 4 := by 
    cases h1b with 
    | inl h => 
      contradiction 
    | inr h => 
      linarith 
  have hc2 : c^2 = 4 := by 
    cases h1c with 
    | inl h => 
      contradiction 
    | inr h => 
      linarith

  have ha1 : a = 2 ∨ a = -2 := by 
    have : a^2 - 4 = 0 := by linarith 
    have : (a - 2) * (a + 2) = 0 := by 
      linarith 
    cases' (mul_eq_zero.mp this) with h1 h2 
    · -- a - 2 = 0:
      left 
      linarith 
    · -- a + 2 = 0:
      right 
      linarith 
  have hb1 : b = 2 ∨ b = -2 := by 
    have : b^2 - 4 = 0 := by linarith 
    have : (b - 2) * (b + 2) = 0 := by 
      linarith 
    cases' (mul_eq_zero.mp this) with h1 h2 
    · -- b - 2 = 0:
      left 
      linarith 
    · -- b + 2 = 0:
      right 
      linarith 
  have hc1 : c = 2 ∨ c = -2 := by 
    have : c^2 - 4 = 0 := by linarith 
    have : (c - 2) * (c + 2) = 0 := by 
      linarith 
    cases' (mul_eq_zero.mp this) with h1 h2 
    · -- c - 2 = 0:
      left 
      linarith 
    · -- c + 2 = 0:
      right 
      linarith 
  rcases ha1 with (ha1 | ha1) <;> rcases hb1 with (hb1 | hb1) <;> rcases hc1 with (hc1 | hc1)
  all_goals 
    norm_num [ha1, hb1, hc1] at ha hb hc
    <;> nlinarith