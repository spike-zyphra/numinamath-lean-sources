import Mathlib

theorem algebra_167433 (x y : ℕ) :
    |(4 * x ^ 2 - 4 * x * y + y ^ 2 - 3 * x - 2 * y + 56 : ℤ)| + 3 * x + 2 * y = 56 ↔
    (x, y) = (0, 0) ∨ (x, y) = (1, 2) ∨ (x, y) = (2, 4) ∨ (x, y) = (3, 6) ∨
    (x, y) = (4, 8) ∨ (x, y) = (5, 10) ∨ (x, y) = (6, 12) ∨ (x, y) = (7, 14) ∨
    (x, y) = (8, 16) := by
  constructor
  · -- Assume the equation holds, prove the disjunction.
    intro h
    have h1 : |(4 * x ^ 2 - 4 * x * y + y ^ 2 - 3 * x - 2 * y + 56 : ℤ)| + 3 * x + 2 * y = (56 : ℤ) := by
      exact_mod_cast h
    have h3 : (4 * x ^ 2 - 4 * x * y + y ^ 2 - 3 * x - 2 * y + 56 : ℤ) = (2 * (x : ℤ) - (y : ℤ)) ^ 2 - 3 * (x : ℤ) - 2 * (y : ℤ) + 56 := by
      have h4 : (4 * x ^ 2 - 4 * x * y + y ^ 2 : ℤ) = (2 * (x : ℤ) - (y : ℤ)) ^ 2 := by
        ring
      rw [show (4 * x ^ 2 - 4 * x * y + y ^ 2 - 3 * x - 2 * y + 56 : ℤ) = (4 * x ^ 2 - 4 * x * y + y ^ 2 : ℤ) - 3 * (x : ℤ) - 2 * (y : ℤ) + 56 by omega]
      rw [h4]
    by_cases h4 : (4 * x ^ 2 - 4 * x * y + y ^ 2 - 3 * x - 2 * y + 56 : ℤ) ≥ 0
    · -- Case where |a| = a.
      rw [abs_of_nonneg h4] at h1
      have h5 : (2 * (x : ℤ) - (y : ℤ)) ^ 2 = 0 := by
        nlinarith
      have h6 : (y : ℤ) = 2 * (x : ℤ) := by
        nlinarith
      have h6' : y = 2 * x := by
        omega
      have h6 : x ≤ 8 := by
        have h8 : (4 * x ^ 2 - 4 * x * y + y ^ 2 - 3 * x - 2 * y + 56 : ℤ) ≥ 0 := h4
        rw [h3] at h8
        rw [show (y : ℤ) = 2 * (x : ℤ) by omega] at h8
        nlinarith
      interval_cases x <;> norm_num [Prod.ext_iff, h6'] at *
      <;> omega
    · -- Case where |a| = -a.
      rw [abs_of_neg (show (4 * x ^ 2 - 4 * x * y + y ^ 2 - 3 * x - 2 * y + 56 : ℤ) < 0 by omega)] at h1
      have h7 : (4 * x ^ 2 - 4 * x * y + y ^ 2 - 3 * x - 2 * y + 56 : ℤ) < 0 := by
        linarith
      nlinarith [sq_nonneg ((2 * (x : ℤ) - (y : ℤ)) : ℤ), sq_nonneg ((x : ℤ) - (y : ℤ) / 2), sq_nonneg ((y : ℤ) - 2 * (x : ℤ)), sq_nonneg ((x : ℤ) - 8 : ℤ), sq_nonneg ((y : ℤ) - 16 : ℤ)]
  · -- Assume the disjunction holds, prove the equation.
    rintro (h | h | h | h | h | h | h | h | h)
    · -- Case where (x, y) = (0, 0).
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case where (x, y) = (1, 2).
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case where (x, y) = (2, 4).
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case where (x, y) = (3, 6).
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case where (x, y) = (4, 8).
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case where (x, y) = (5, 10).
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case where (x, y) = (6, 12).
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case where (x, y) = (7, 14).
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case where (x, y) = (8, 16).
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      norm_num