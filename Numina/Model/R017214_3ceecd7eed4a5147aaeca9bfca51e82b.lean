import Mathlib

theorem number_theory_239193 (a b c : ℤ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : a + b + c = 97) :
    min (min a b) c ≤ 32 := by
  by_contra h
  push_neg at h
  have h6 : min (min a b) c > 32 := h
  -- if h6, then a > 32, b > 32 and c > 32
  have h7 : a > 32 := by
    by_contra h8
    push_neg at h8
    have h8 : a ≤ 32 := by linarith
    -- min (min a b) c ≤ a
    have h9 : min (min a b) c ≤ a := by
      have : min (min a b) c ≤ min a b := by apply min_le_left
      have : min a b ≤ a := by apply min_le_left
      linarith
    linarith
  -- Similarly for b and c
  have h8 : b > 32 := by
    by_contra h8
    push_neg at h8
    have h12 : b ≤ 32 := by linarith
    have h13 : min (min a b) c ≤ b := by
      have : min (min a b) c ≤ min a b := by apply min_le_left
      have : min a b ≤ b := by apply min_le_right
      linarith
    linarith
  have h9 : c > 32 := by
    by_contra h9
    push_neg at h9
    have h14 : c ≤ 32 := by linarith
    have h15 : min (min a b) c ≤ c := by apply min_le_right
    linarith
  have h10 : a ≥ 33 := by omega
  have h11 : b ≥ 33 := by omega
  have h12 : c ≥ 33 := by omega
  have h13 : a + b + c ≥ 99 := by
    linarith
  linarith