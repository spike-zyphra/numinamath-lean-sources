import Mathlib

theorem number_theory_613455     (a b c : ℕ)
    -- Assumptions that a, b, and c are positive natural numbers
    (h₀ : 0 < a)
    (h₁ : 0 < b)
    (h₂ : 0 < c)
    -- The main equation: 4/a + 2/b = 1/c as rational numbers
    (h₃ : (4 / a : ℚ) + (2 / b : ℚ) = 1 / c) :
    IsSquare (a ^ 2 + 4 * b ^ 2 + 16 * c ^ 2) := by
  have h4 : (a : ℚ) > 0 := by exact_mod_cast h₀
  have h5 : (b : ℚ) > 0 := by exact_mod_cast h₁
  have h6 : (c : ℚ) > 0 := by exact_mod_cast h₂
  have eq1 : (a : ℚ) * (b : ℚ) = 4 * (b * (c : ℚ)) + 2 * ((a : ℚ) * (c : ℚ)) := by
    have eq2 : (4 / a : ℚ) + (2 / b : ℚ) = 1 / c := h₃
    have h7 : (a : ℚ) ≠ 0 := by positivity
    have h8 : (b : ℚ) ≠ 0 := by positivity
    have h9 : (c : ℚ) ≠ 0 := by positivity
    field_simp [h7, h8, h9] at eq2 ⊢
    ring_nf at eq2 ⊢
    nlinarith
  have eq4 : (a : ℤ) * (b : ℤ) = 4 * (b * (c : ℤ)) + 2 * ((a : ℤ) * (c : ℤ)) := by
    have eq2' : (a : ℚ) * (b : ℚ) = 4 * (b * (c : ℚ)) + 2 * ((a : ℚ) * (c : ℚ)) := eq1
    have h7 : (a : ℚ) = (a : ℤ) := by simp
    have h8 : (b : ℚ) = (b : ℤ) := by simp
    have h9 : (c : ℚ) = (c : ℤ) := by simp
    rw [h7, h8, h9] at eq2'
    exact_mod_cast eq2'
  have eq5 : (a ^ 2 + 4 * b ^ 2 + 16 * c ^ 2 : ℤ) = (a + 2 * b - 4 * c : ℤ) ^ 2 := by
    have eq6 : (a : ℤ) * (b : ℤ) = 4 * (b * (c : ℤ)) + 2 * ((a : ℤ) * (c : ℤ)) := eq4
    nlinarith [sq_nonneg (a - 2 * b + 4 * c : ℤ), sq_nonneg (a - 4 * c : ℤ), sq_nonneg (2 * b - 4 * c : ℤ)]
  have eq6 : IsSquare ((a ^ 2 + 4 * b ^ 2 + 16 * c ^ 2) : ℤ) := by
    have eq7 : (a ^ 2 + 4 * b ^ 2 + 16 * c ^ 2 : ℤ) = (a + 2 * b - 4 * c : ℤ) ^ 2 := eq5
    rw [eq7]
    exact ⟨a + 2 * b - 4 * c, by ring⟩
  have eq7 : IsSquare (a ^ 2 + 4 * b ^ 2 + 16 * c ^ 2) := by
    exact_mod_cast eq6
  exact_mod_cast eq7