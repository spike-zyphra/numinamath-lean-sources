import Mathlib

theorem algebra_11302 : IsLeast { a₃ + 20 | (a₁ : ℝ) (a₂ : ℝ) (a₃ : ℝ) (d : ℝ) (q : ℝ) (h₀ : q ≠ 0) (h₁ : a₁ = 9) (h₂ : a₂ = a₁ + d) (h₃ : a₃ = a₁ + 2 * d) (h₄ : a₂ + 2 = a₁ * q) (h₅ : a₃ + 20 = (a₂ + 2) * q) } 1 := by
  constructor
  · -- Show that 1 belongs to the set
    use 9, -5, -19, -14, -1 / 3
    norm_num
  · -- We need to prove that no value less than 1 is in the set
    intro r hr
    rcases hr with ⟨a₁, a₂, a₃, d, q, h₀, h₁, h₂, h₃, h₄, h₅, hr⟩
    have ha₂' : a₂ = 9 + d := by
      linarith [h₁, h₂]
    have ha₃ : a₃ = 9 + 2 * d := by
      linarith [h₁, h₃]
    rw [ha₃] at h₅
    rw [ha₃] at hr
    have h4' : (9 + d) + 2 = 9 * q := by
      rw [show a₁ = 9 by linarith [h₁]] at h₄
      have ha₂'' : a₂ = (9 : ℝ) + d := by
        linarith [h₁, h₂]
      rw [ha₂''] at h₄
      linarith
    have eq3 : 9 * q = 11 + d := by
      linarith [h4']
    have h7 : q = (11 + d) / 9 := by
      have h8 : q = (11 + d) / 9 := by
        have h9 : 9 * q = 11 + d := eq3
        field_simp [h₀] at *
        linarith [h9]
      linarith [h8]
    rw [h7] at h₅
    have h6 : d ^ 2 + 4 * d - 140 = 0 := by
      nlinarith
    have h7 : (d - 10) * (d + 14) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h7) with h8 h9
    · -- Case where d = 10:
      have h10 : d = 10 := by linarith
      nlinarith
    · -- Case where d = -14:
      have h14 : d = -14 := by linarith
      nlinarith