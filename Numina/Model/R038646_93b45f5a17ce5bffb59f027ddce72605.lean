import Mathlib

theorem number_theory_239057 (a b : ℤ) (h₀ : 7 ∣ a + b)
    (h₁ : a - b = c) (h₂ : b - c = d) (h₃ : c - d = e)
    (h₄ : d - e = f) (h₅ : e - f = g) :
    7 ∣ a^2 + b^2 + c^2 + d^2 + e^2 + f^2 + g^2 := by
  have h6 : c = a - b := by linarith
  have h7 : d = 2 * b - a := by 
    linarith [h₁, h₂, h6]
  have h8 : e = 2 * a - 3 * b := by
    linarith [h₃, h6, h7]
  have h10 : f = 5 * b - 3 * a := by
    linarith [h₄, h₃, h6, h7, h8]
  have h11 : g = 5 * a - 8 * b := by
    linarith [h₅, h8, h10]
  have h12 : a % 7 = 0 ∨ a % 7 = 1 ∨ a % 7 = 2 ∨ a % 7 = 3 ∨ a % 7 = 4 ∨ a % 7 = 5 ∨ a % 7 = 6 := by 
    omega
  have h13 : b % 7 = 0 ∨ b % 7 = 1 ∨ b % 7 = 2 ∨ b % 7 = 3 ∨ b % 7 = 4 ∨ b % 7 = 5 ∨ b % 7 = 6 := by 
    omega
  rcases h12 with ha | ha | ha | ha | ha | ha | ha <;> rcases h13 with hb | hb | hb | hb | hb | hb | hb <;> 
    simp [ha, hb, h6, h7, h8, h10, h11, Int.dvd_iff_emod_eq_zero, Int.add_emod, Int.mul_emod, pow_two, Int.sub_emod] at h₀ ⊢ 
    <;> omega