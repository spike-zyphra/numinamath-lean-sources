import Mathlib

theorem number_theory_235497 (a b c : ℤ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : (a + 1) * (b + 1) * (c - 2) = a * b * c) :
    3 ∣ a ∨ 3 ∣ b ∨ 3 ∣ c := by 
  by_contra h
  push_neg at h
  have h₄ : a % 3 = 1 ∨ a % 3 = 2 := by
    omega
  have h₅ : b % 3 = 1 ∨ b % 3 = 2 := by
    omega
  have h₆ : c % 3 = 1 ∨ c % 3 = 2 := by
    omega
  have eq1 : (a + 1) * (b + 1) * (c - 2) % 3 = (a * b * c) % 3 := by
    omega
  rcases h₄ with (ha | ha)
  <;> rcases h₅ with (hb | hb)
    <;> rcases h₆ with (hc | hc)
      <;> simp [Int.add_emod, Int.mul_emod, Int.sub_emod, ha, hb, hc] at eq1
        <;> omega