import Mathlib

theorem algebra_162884 (p : ℝ) (hp : p ≥ 0) (a b c : ℝ)
    (h₀ : a = p - 2) (h₁ : b = 3 * Real.sqrt p) (h₂ : c = -8 - p)
    (h₃ : ∃ r, b = a * r ∧ c = b * r) :
    p = 1 := by

  rcases h₃ with ⟨r, h₄, h₅⟩
  have h₆ : b ^ 2 = a * c := by
    have eq1 : b = a * r := h₄
    have eq2 : c = b * r := h₅
    rw [eq2, eq1]
    nlinarith [sq_nonneg (a * r), sq_nonneg ((a * r) * r), sq_nonneg (a * r * r), sq_nonneg (a * (r ^ 2))]

  rw [h₀] at h₆
  rw [h₁] at h₆
  rw [h₂] at h₆

  have h₈ : (3 * Real.sqrt p) ^ 2 = 9 * p := by
    calc
      (3 * Real.sqrt p) ^ 2 = 9 * (Real.sqrt p) ^ 2 := by ring
      _ = 9 * p := by rw [Real.sq_sqrt]; linarith

  rw [h₈] at h₆

  have h₉ : p ^ 2 + 15 * p - 16 = 0 := by
    nlinarith [Real.sqrt_nonneg p]

  have hp_eq : p = 1 := by
    have h10 : p ^ 2 + 15 * p - 16 = 0 := h₉
    have h11 : (p - 1) * (p + 16) = 0 := by 
      nlinarith
    cases' (mul_eq_zero.mp h11) with h12 h13
    · 
      linarith
    · 
      nlinarith

  exact hp_eq