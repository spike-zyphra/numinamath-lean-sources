import Mathlib

theorem algebra_112559 (x y : ℤ) :
    x + y = 1 ∧ x^2 + 2 * x + y^2 = 9 ↔ (x = 2 ∧ y = -1) ∨ (x = -2 ∧ y = 3) := by 
  constructor 
  · -- Assume (x + y = 1 ∧ x^2 + 2 * x + y^2 = 9), prove (x = 2 ∧ y = -1) ∨ (x = -2 ∧ y = 3)
    intro h 
    rcases h with ⟨h1, h2⟩
    have h3 : y = 1 - x := by linarith 
    rw [h3] at h2 
    have h5 : 2 * x^2 = 8 := by 
      nlinarith 
    have h6 : x ^ 2 = 4 := by 
      nlinarith 
    have h7 : x = 2 ∨ x = -2 := by 
      have h8 : x ^ 2 - 4 = 0 := by 
        linarith 
      have h9 : (x - 2) * (x + 2) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.mp h9) with h10 h11 
      · -- case h10
        left 
        linarith 
      · -- case h11 
        right 
        linarith 
    cases h7 with 
    | inl hx2 => 
      left 
      have hy1 : y = -1 := by 
        rw [hx2] at h3 
        linarith 
      exact ⟨hx2, hy1⟩ 
    | inr hx2 => 
      right 
      have hy3 : y = 3 := by 
        rw [hx2] at h3 
        linarith 
      exact ⟨hx2, hy3⟩ 
  · -- Assume (x = 2 ∧ y = -1) ∨ (x = -2 ∧ y = 3), prove x + y = 1 ∧ x^2 + 2 * x + y^2 = 9
    rintro (h | h)
    · -- Case h: x = 2 ∧ y = -1
      rcases h with ⟨hx, hy⟩
      constructor 
      · -- Prove x + y = 1
        linarith 
      · -- Prove x^2 + 2 * x + y^2 = 9
        rw [hx, hy] 
        norm_num 
    · -- Case h: x = -2 ∧ y = 3
      rcases h with ⟨hx, hy⟩
      constructor 
      · -- Prove x + y = 1
        linarith 
      · -- Prove x^2 + 2 * x + y^2 = 9
        rw [hx, hy] 
        norm_num