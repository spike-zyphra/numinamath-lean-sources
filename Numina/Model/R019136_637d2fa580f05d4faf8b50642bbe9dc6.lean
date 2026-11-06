import Mathlib
open Int

theorem algebra_1442 (x : ℝ) (hx : 4 * (x - ⌊x⌋) = x + ⌊x⌋) : x = 0 ∨ x = 5 / 3 := by
  have h1 : (⌊x⌋ : ℝ) ≤ x := by exact Int.floor_le x
  have h2 : x < (⌊x⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one x
  have h3 : (3 * x : ℝ) = 5 * (⌊x⌋ : ℝ) := by
    have h4 : (4 * (x - ⌊x⌋) : ℝ) = x + (⌊x⌋ : ℝ) := by
      linarith [hx]
    ring_nf at h4 ⊢
    linarith
  have h4 : ⌊x⌋ ≤ 1 := by
    by_contra h
    push_neg at h
    have h5 : ⌊x⌋ ≥ 2 := by omega
    have h6 : (⌊x⌋ : ℝ) ≥ (2 : ℝ) := by exact_mod_cast h5
    nlinarith [h1, h2, h3, h6]
  have h5 : ⌊x⌋ ≥ 0 := by
    by_contra h
    push_neg at h
    have h6 : ⌊x⌋ ≤ -1 := by omega
    have h7 : (⌊x⌋ : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast h6
    nlinarith [h1, h2, h3, h7]
  have h6 : ⌊x⌋ = 0 ∨ ⌊x⌋ = 1 := by omega
  cases h6 with
  | inl h7 =>
    have h8 : (⌊x⌋ : ℝ) = (0 : ℝ) := by exact_mod_cast h7
    have hx0 : x = 0 := by
      nlinarith [h3, h8]
    left
    exact hx0
  | inr h7 =>
    have h8 : (⌊x⌋ : ℝ) = (1 : ℝ) := by exact_mod_cast h7
    have hx1 : x = 5 / 3 := by
      nlinarith [h3, h8]
    right
    exact hx1