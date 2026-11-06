import Mathlib

theorem number_theory_7174 (x : ZMod 19) :
    x ^ 6 = 11 ↔ x = 4 ∨ x = 13 ∨ x = 9 ∨ x = 15 ∨ x = 6 ∨ x = 10 := by
  constructor
  · -- Assume x^6 = 11, prove x is one of the six roots
    intro h
    have h1 : x ^ 6 = 11 := h
    have : x = 4 ∨ x = 13 ∨ x = 9 ∨ x = 15 ∨ x = 6 ∨ x = 10 := by 
      fin_cases x <;> simp [pow_succ, ZMod] at h1 ⊢ <;> tauto
    assumption
  · -- Assume x is one of the six roots, prove x^6 = 11
    rintro (h | h | h | h | h | h)
    · -- x = 4
      rw [h]
      native_decide
    · -- x = 13
      rw [h]
      native_decide
    · -- x = 9
      rw [h]
      native_decide
    · -- x = 15
      rw [h]
      native_decide
    · -- x = 6
      rw [h]
      native_decide
    · -- x = 10
      rw [h]
      native_decide