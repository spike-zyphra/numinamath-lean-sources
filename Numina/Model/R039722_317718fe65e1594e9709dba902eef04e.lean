import Mathlib

theorem number_theory_128661 (a b c d : ℤ) :
    12 ∣ (a - b) * (c - d) * (a - c) * (b - d) * (a - d) * (b - c) := by
  have h1 : (a - b) * (c - d) * (a - c) * (b - d) * (a - d) * (b - c) % 3 = 0 := by
    have h1 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
    have h2 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
    have h3 : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 := by omega
    have h4 : d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 := by omega
    rcases h1 with (ha | ha | ha) <;> rcases h2 with (hb | hb | hb) <;> rcases h3 with (hc | hc | hc) <;> rcases h4 with (hd | hd | hd) <;> simp [Int.mul_emod, Int.sub_emod, ha, hb, hc, hd]
  have h2 : (a - b) * (c - d) * (a - c) * (b - d) * (a - d) * (b - c) % 4 = 0 := by
    have h1 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
    have h2 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
    have h3 : c % 4 = 0 ∨ c % 4 = 1 ∨ c % 4 = 2 ∨ c % 4 = 3 := by omega
    have h4 : d % 4 = 0 ∨ d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by omega
    rcases h1 with (ha | ha | ha | ha) <;> rcases h2 with (hb | hb | hb | hb) <;> rcases h3 with (hc | hc | hc | hc) <;> rcases h4 with (hd | hd | hd | hd) <;> simp [Int.mul_emod, Int.sub_emod, ha, hb, hc, hd]
  omega