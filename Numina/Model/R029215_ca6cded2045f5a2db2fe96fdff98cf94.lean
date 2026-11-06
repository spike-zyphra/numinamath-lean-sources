import Mathlib

theorem number_theory_7333 (x : Fin 127) :
    x^2 ≡ 73 [MOD 127] ↔ x = 33 ∨ x = 94 := by 
  constructor
  · -- Assume x^2 ≡ 73 [MOD 127], prove x = 33 ∨ x = 94
    intro h 
    simp [Nat.ModEq] at h 
    have : x = 33 ∨ x = 94 := by 
      have h2 : x = 33 ∨ x = 94 := by 
        fin_cases x <;> simp [Nat.ModEq] at h ⊢ <;> native_decide 
      exact h2 
    exact this 
  · -- Assume x = 33 ∨ x = 94, prove x^2 ≡ 73 [MOD 127]
    rintro (h | h)
    · -- Case x = 33 
      rw [h] 
      simp [Nat.ModEq]
      <;> native_decide 
    · -- Case x = 94 
      rw [h] 
      simp [Nat.ModEq]
      <;> native_decide