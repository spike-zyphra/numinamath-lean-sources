import Mathlib

theorem algebra_11210 {x : ℚ} (hx : x = 13 / 3 - ⌊x⌋) :
    x = 7 / 3 := by 
  have h1 : ⌊x⌋ ≤ (x : ℚ) := by
    exact Int.floor_le x
  have h2 : (x : ℚ) < (⌊x⌋ + 1 : ℚ) := by
    exact Int.lt_floor_add_one x
  have h3 : ⌊x⌋ ≤ 2 := by
    by_contra h
    push_neg at h
    have h4 : ⌊x⌋ ≥ 3 := by
      omega
    have h7 : (⌊x⌋ : ℚ) ≥ 3 := by
      exact_mod_cast h4
    have h8 : x ≤ 4 / 3 := by
      linarith [hx, h7]
    have h9 : (⌊x⌋ : ℚ) ≤ (x : ℚ) := by
      exact_mod_cast h1
    nlinarith [h9, h7, h8]
  have h4 : ⌊x⌋ ≥ 2 := by
    by_contra h
    push_neg at h
    have h4 : ⌊x⌋ ≤ 1 := by
      omega
    have h5 : (⌊x⌋ : ℚ) ≤ 1 := by
      exact_mod_cast h4
    have h6 : x ≥ 10 / 3 := by
      linarith [hx, h5]
    have h7 : x < (⌊x⌋ + 1 : ℚ) := by
      exact_mod_cast h2
    have h8 : (⌊x⌋ + 1 : ℚ) ≤ (2 : ℚ) := by
      have h9 : ⌊x⌋ + 1 ≤ 2 := by
        omega
      have h10 : (⌊x⌋ + 1 : ℚ) ≤ (2 : ℚ) := by
        exact_mod_cast h9
      linarith
    nlinarith [h6, h7, h8]
  have h5 : ⌊x⌋ = 2 := by
    omega
  have h6 : x = 7 / 3 := by
    rw [show ⌊x⌋ = (2 : ℤ) by omega] at hx
    norm_num at hx ⊢
    linarith
  exact_mod_cast h6