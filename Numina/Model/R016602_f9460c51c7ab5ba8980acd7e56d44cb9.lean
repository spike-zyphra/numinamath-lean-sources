import Mathlib

theorem algebra_16243 (a b c : ℝ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : a^2 + b^2 = c^2) (h₄ : c = 5) (h₅ : min (min a b) c = 3) :
    (1 / 2) * a * b = 6 := by
  have h6 : min (min a b) c = 3 := h₅
  rw [h₄] at h6
  have h7 : min a b = 3 := by
    by_cases h8 : min a b ≤ (5 : ℝ)
    · -- In this case, min (min a b) 5 = min a b
      have h9 : min (min a b) (5 : ℝ) = min a b := by
        apply min_eq_left
        linarith
      rw [h9] at h6
      linarith
    · -- In this case, min (min a b) 5 = 5
      have h10 : min (min a b) (5 : ℝ) = (5 : ℝ) := by
        apply min_eq_right
        linarith
      rw [h10] at h6
      linarith
  cases min_cases a b with
  | inl h9 =>
    have ha : a = 3 := by
      linarith [h9, h7]
    have hb : b = 4 := by
      rw [h₄] at h₃
      rw [ha] at h₃
      nlinarith
    rw [ha, hb]
    norm_num
  | inr h9 =>
    have hb : b = 3 := by
      linarith [h9, h7]
    have ha : a = 4 := by
      rw [h₄] at h₃
      rw [hb] at h₃
      nlinarith
    rw [ha, hb]
    norm_num