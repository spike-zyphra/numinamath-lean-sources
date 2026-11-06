import Mathlib

theorem algebra_228664 :
    {(a, b) : ℕ × ℕ | |(a : ℤ) - b| + a * b = 1}.ncard = 3 := by
  have h1 : {(a, b) : ℕ × ℕ | |(a : ℤ) - b| + a * b = 1} = {(0, 1), (1, 0), (1, 1)} := by
    ext ⟨a, b⟩
    simp
    constructor
    · -- Prove that if `(a, b)` is in the set, then `(a, b)` must be one of `(0, 1)`, `(1, 0)`, or `(1, 1)`.
      intro h
      have h' : (a : ℤ) ≥ 0 := by exact_mod_cast (show (a : ℕ) ≥ 0 by omega)
      have h'' : (b : ℤ) ≥ 0 := by exact_mod_cast (show (b : ℕ) ≥ 0 by omega)
      by_cases h_eq : (a : ℤ) ≥ (b : ℤ)
      · -- If `a ≥ b`, then `|a - b| = a - b`.
        rw [abs_of_nonneg (show (a : ℤ) - (b : ℤ) ≥ 0 by linarith)] at h
        have h2 : a ≤ 1 := by
          nlinarith [sq_nonneg ((a : ℤ) - 1 : ℤ), sq_nonneg ((b : ℤ) - 1 : ℤ), 
            mul_nonneg (show (0 : ℤ) ≤ (a : ℤ) by linarith) (show (0 : ℤ) ≤ (b : ℤ) by linarith)]
        have h3 : b ≤ 1 := by
          omega
        interval_cases a <;> interval_cases b <;> omega
      · -- Case where `a < b`, so `|a - b| = b - a`.
        rw [abs_of_neg (show (a : ℤ) - (b : ℤ) < 0 by linarith)] at h
        have h2 : b ≤ 1 := by
          nlinarith [sq_nonneg ((a : ℤ) - 1 : ℤ), sq_nonneg ((b : ℤ) - 1 : ℤ), 
            mul_nonneg (show (0 : ℤ) ≤ (a : ℤ) by linarith) (show (0 : ℤ) ≤ (b : ℤ) by linarith)]
        have h3 : a ≤ 1 := by
          omega
        interval_cases a <;> interval_cases b <;> omega
    · -- Prove the reverse: each pair in `{(0,1), (1,0), (1,1)}` is in the set.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · norm_num
      · norm_num
      · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  native_decide