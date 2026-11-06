import Mathlib

theorem number_theory_7337 (x : ZMod 41) :
    x^2 = -4 ↔ x = 18 ∨ x = -18 := by
  constructor
  · -- Assume x^2 = -4, prove x = 18 ∨ x = -18
    intro h_eq
    have h1 : x = 18 ∨ x = -18 := by 
      have h2 : x ^ 2 = -4 := h_eq
      fin_cases x <;> simp [pow_two] at h2 ⊢ <;> try { 
        norm_num at h2 ⊢ 
        <;> tauto 
      }
      <;> try { contradiction }
    exact h1
  · -- Assume x = 18 ∨ x = -18, prove x^2 = -4
    intro h_eq
    rcases h_eq with (h_eq | h_eq)
    · -- x = 18
      rw [h_eq]
      native_decide
    · -- x = -18
      rw [h_eq]
      native_decide