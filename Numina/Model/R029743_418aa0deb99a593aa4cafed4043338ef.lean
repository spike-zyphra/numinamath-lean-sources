import Mathlib

theorem number_theory_308137 (x : ℤ) :
    120 ∣ 7 * x ^ 5 + x ^ 3 - x + 2 ↔ ∃ k, x = 120 * k + 34 := by
  constructor
  · -- Assume 120 divides the polynomial, prove ∃ k, x = 120 * k + 34
    intro h
    have h1 : (7 * x ^ 5 + x ^ 3 - x + 2) % 8 = 0 := by
      omega
    have h2 : (7 * x ^ 5 + x ^ 3 - x + 2) % 3 = 0 := by
      omega
    have h3 : (7 * x ^ 5 + x ^ 3 - x + 2) % 5 = 0 := by
      omega
    have h4 : x % 8 = 2 := by
      have : x % 8 = 2 := by
        have h1' : (7 * x ^ 5 + x ^ 3 - x + 2) % 8 = 0 := h1
        have : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by 
          omega
        rcases this with (h | h | h | h | h | h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod] at h1' <;> omega
      assumption
    have h5 : x % 3 = 1 := by
      have h2' : (7 * x ^ 5 + x ^ 3 - x + 2) % 3 = 0 := h2
      have : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by 
        omega
      rcases this with (h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod] at h2' <;> omega
    have h6 : x % 5 = 4 := by 
      have h3' : (7 * x ^ 5 + x ^ 3 - x + 2) % 5 = 0 := h3
      have : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by 
        omega
      rcases this with (h | h | h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod] at h3' <;> omega
    refine' ⟨(x - 34) / 120, by omega⟩
  · -- Assume ∃ k, x = 120 * k + 34
    rintro ⟨k, hk⟩
    have h8 : (7 * x ^ 5 + x ^ 3 - x + 2) % 8 = 0 := by
      rw [show x = 120 * k + 34 by linarith]
      have : (7 * (120 * k + 34) ^ 5 + (120 * k + 34) ^ 3 - (120 * k + 34) + 2) % 8 = 0 := by
        have h1 : (120 * k + 34) % 8 = 2 := by
          omega
        simp [h1, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod]
      omega
    have h3 : (7 * x ^ 5 + x ^ 3 - x + 2) % 3 = 0 := by
      rw [show x = 120 * k + 34 by linarith]
      have : (7 * (120 * k + 34) ^ 5 + (120 * k + 34) ^ 3 - (120 * k + 34) + 2) % 3 = 0 := by
        have h1 : (120 * k + 34) % 3 = 1 := by
          omega
        simp [h1, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod]
      omega
    have h5 : (7 * x ^ 5 + x ^ 3 - x + 2) % 5 = 0 := by
      rw [show x = 120 * k + 34 by linarith]
      have : (7 * (120 * k + 34) ^ 5 + (120 * k + 34) ^ 3 - (120 * k + 34) + 2) % 5 = 0 := by
        have h1 : (120 * k + 34) % 5 = 4 := by
          omega
        simp [h1, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod]
      omega
    omega