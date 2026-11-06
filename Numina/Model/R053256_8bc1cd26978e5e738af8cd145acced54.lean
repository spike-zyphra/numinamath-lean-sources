import Mathlib

theorem algebra_302867 {m n : ℤ} (h : ∃ x1 x2 : ℤ, x1^2 * (1 + m^2) - 2 * m * (1 + n) * x1 + m^2 + n^2 = 0 ∧
    x2^2 * (1 + m^2) - 2 * m * (1 + n) * x2 + m^2 + n^2 = 0 ∧ x1 = m ∧ x2 = m) :
    m^2 = n := by
  rcases h with ⟨x1, x2, h₁, h₂, hx1, hx2⟩
  rw [hx1] at h₁
  rw [hx2] at h₂
  -- Let's compute the equation with x1 = m:
  -- m^2 * (1 + m^2) - 2 * m * (1 + n) * m + m^2 + n^2 = 0
  -- Expanding:
  -- m^4 + m^2 - 2m^2(1+n) + m^2 + n^2 = 0
  -- m^4 + m^2 - 2m^2 - 2m^2n + m^2 + n^2 = 0
  -- m^4 + (1-2+1)m^2 + n^2 - 2m^2n = 0
  -- m^4 + 0 + n^2 - 2m^2n = 0
  -- m^4 + n^2 - 2m^2n = 0
  -- This is (n - m^2)^2 = 0
  have eq1 : (n - m^2)^2 = 0 := by
    nlinarith
  have h_zero : n - m^2 = 0 := by
    apply pow_eq_zero 
    exact eq1
  linarith