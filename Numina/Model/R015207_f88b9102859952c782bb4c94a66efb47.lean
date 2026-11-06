import Mathlib

theorem number_theory_6587 (x : ZMod 23) : x^8 = 41 ↔ x = 6 ∨ x = -6 := by 
  have h1 : (41 : ZMod 23) = (18 : ZMod 23) := by 
    native_decide 
  have h2 : x^8 = 41 ↔ x^8 = 18 := by 
    rw [h1]
  rw [h2]
  constructor 
  · -- Assume x ^ 8 = 18, need to prove x = 6 ∨ x = -6 
    intro h_eq 
    have h3 : x^8 = 18 := h_eq 
    -- Now, we'll need to, by substitution, check all possible residues
    have h4 : x = 6 ∨ x = -6 := by 
      have h5 : x ^ 8 = 18 := h_eq 
      have h6 : x = (x : ZMod 23) := by simp 
      fin_cases x <;> simp [pow_succ, pow_zero, mul_add, mul_assoc] at h5 ⊢ 
      <;> try { 
        tauto 
      }
      <;> try { 
        norm_num at h5 ⊢ 
        <;> tauto 
        <;> omega 
      }
    assumption 
  · -- Assume x = 6 ∨ x = -6, prove x^8 = 18 
    rintro (r | r)
    · -- x = 6 
      rw [r]
      native_decide 
    · -- x = -6 
      rw [r]
      native_decide