import Mathlib

theorem algebra_257337 {b h : ℕ} (hb : b = h - 4) (h₀ : b * h ≠ 0)
    (h₁ : (1 / 2) * b * h = 96) :
    b = 12 ∧ h = 16 := by
  have h2 : (1 / 2 : ℕ) = 0 := by
    norm_num
  have h2' : (1 / 2 : ℕ) * b * h = 0 := by
    rw [show (1 / 2 : ℕ) = 0 by
      norm_num
    ]
    <;> simp
  -- Now h₁ : (1 / 2) * b * h = 96
  omega