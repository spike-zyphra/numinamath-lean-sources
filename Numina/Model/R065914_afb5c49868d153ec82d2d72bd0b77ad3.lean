import Mathlib

theorem algebra_139758 (a b : ℤ) : 3 * a^2 * b^2 + b^2 = 517 + 30 * a^2 ↔
    (a, b) = (2, 7) ∨ (a, b) = (-2, 7) ∨ (a, b) = (2, -7) ∨ (a, b) = (-2, -7) := by
  constructor
  · -- First direction: equation implies the four solutions
    rintro h
    have h1 : b^2 * (3 * a^2 + 1) = 517 + 30 * a^2 := by
      nlinarith
    -- Rewrite the equation as (b^2 - 10) * (3a^2 + 1) = 507
    have h2 : (b^2 - 10) * (3 * a^2 + 1) = 507 := by
      nlinarith
    -- Let's show that 3a^2 + 1 divides 507
    have h3 : (3 * a^2 + 1) ∣ 507 := by
      use (b^2 - 10)
      nlinarith
    have h4 : (3 * a^2 + 1) ≥ 1 := by
      nlinarith [sq_nonneg (a : ℤ)]
    have h5 : (3 * a^2 + 1) ≤ 507 := by
      exact Int.le_of_dvd (by norm_num) h3
    have h6 : a ≤ 12 := by
      nlinarith [sq_nonneg (a : ℤ)]
    have h7 : a ≥ -13 := by
      nlinarith [sq_nonneg (a : ℤ)]
    interval_cases a <;> try { 
      norm_num at h1 h2 ⊢ 
      <;> try { 
        have h8 : b ≤ 23 := by nlinarith [sq_nonneg (b : ℤ)]
        have h9 : b ≥ -24 := by nlinarith [sq_nonneg (b : ℤ)]
        interval_cases b <;> norm_num at h1 h2 ⊢ 
        <;> tauto 
      }
    }
  · -- Second direction: the four solutions satisfy the equation
    rintro (h | h | h | h)
    · -- (2, 7)
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- (-2, 7)
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- (2, -7)
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- (-2, -7)
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      norm_num