import Mathlib

theorem number_theory_259854 (x y z : ℕ) (h₀ : 0 < x) (h₁ : 0 < y) (h₂ : 0 < z)
    (h₃ : x ≤ y) (h₄ : y ≤ z) (h₅ : 5 * (x * y + y * z + z * x) = 4 * x * y * z) :
    (x, y, z) = (2, 5, 10) ∨ (x, y, z) = (2, 4, 20) := by
  have h6 : x ≤ y := h₃
  have h7 : y ≤ z := h₄
  have h8 : x ≤ 5 := by
    nlinarith [h₅, mul_pos h₀ h₁, mul_pos h₁ h₂, mul_pos h₀ h₂]
  interval_cases x <;> try {
    have h9 : y ≤ 10 := by
      nlinarith [h₅, mul_pos h₀ h₁, mul_pos h₁ h₂, mul_pos h₀ h₂]
    interval_cases y <;> try {
      have h10 : z ≤ 20 := by
        nlinarith [h₅, mul_pos h₀ h₁, mul_pos h₁ h₂, mul_pos h₀ h₂]
      interval_cases z <;> try { 
        simp [Prod.ext_iff] at *
        <;> omega
      }
    }
  }