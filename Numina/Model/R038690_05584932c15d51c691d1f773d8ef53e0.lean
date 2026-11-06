import Mathlib

theorem algebra_327976 (x : ℕ → ℤ)
    (hx1 : x 1 = 1)
    (hxn : ∀ k ≥ 2, x k = x (k - 1) + 1 - 4 * ((k - 1) / 4 - (k - 2) / 4)) :
    x 2010 = 2 := by
  have h1 : ∀ k, x (4 * k + 1) = 1 := by
    intro k
    induction k with
    | zero =>
      norm_num [hxn, hx1]
    | succ k ih =>
      have h2 : x (4 * k + 1) = 1 := ih
      have h21 : x (4 * k + 2) = 2 := by
        have h22 : x (4 * k + 2) = x (4 * k + 1) + 1 - 4 * (( (4 * k + 2 - 1) / 4 ) - ( (4 * k + 2 - 2 ) / 4 )) := hxn (4 * k + 2) (by omega)
        simp [h2, show (4 * k + 1: ℕ) = 4 * k + 1 by omega] at h22 ⊢ 
        omega
      have h31 : x (4 * k + 3) = 3 := by
        have h32 : x (4 * k + 3) = x (4 * k + 2) + 1 - 4 * (( (4 * k + 3 - 1) / 4 ) - ( (4 * k + 3 - 2 ) / 4 )) := hxn (4 * k + 3) (by omega)
        simp [h21, show (4 * k + 2: ℕ) = 4 * k + 2 by omega] at h32 ⊢
        omega
      have h41 : x (4 * k + 4) = 4 := by
        have h42 : x (4 * k + 4) = x (4 * k + 3) + 1 - 4 * (( (4 * k + 4 - 1) / 4 ) - ( (4 * k + 4 - 2 ) / 4 )) := hxn (4 * k + 4) (by omega)
        simp [h31, show (4 * k + 3: ℕ) = 4 * k + 3 by omega] at h42 ⊢
        omega
      have h51 : x (4 * k + 5) = 1 := by
        have h52 : x (4 * k + 5) = x (4 * k + 4) + 1 - 4 * (( (4 * k + 5 - 1) / 4 ) - ( (4 * k + 5 - 2 ) / 4 )) := hxn (4 * k + 5) (by omega)
        simp [h41, show (4 * k + 4: ℕ) = 4 * k + 4 by omega] at h52 ⊢
        omega
      have h52 : 4 * (k + 1) + 1 = 4 * k + 5 := by 
        omega 
      rw [h52]
      linarith 
  have h2010 : x 2010 = 2 := by
    have h2 : ∀ k, x (4 * k + 2) = 2 := by
      intro k
      have h11 : x (4 * k + 1) = 1 := h1 k
      have h21 : x (4 * k + 2) = 2 := by
        have h22 : x (4 * k + 2) = x (4 * k + 1) + 1 - 4 * (( (4 * k + 2 - 1) / 4 ) - ( (4 * k + 2 - 2 ) / 4 )) := hxn (4 * k + 2) (by omega)
        simp [h11, show (4 * k + 1: ℕ) = 4 * k + 1 by omega] at h22 ⊢ 
        omega
      exact h21
    have h3 : 2010 = 4 * 502 + 2 := by 
      omega
    rw [h3]
    exact h2 502
  exact h2010