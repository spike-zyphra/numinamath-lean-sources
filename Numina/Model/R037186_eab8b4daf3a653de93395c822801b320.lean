import Mathlib

theorem number_theory_125666 :
    IsLeast {p : ℕ | p.Prime ∧ IsSquare (5 * p^2 + p^3)} 11 := by 
  constructor 
  · -- Show 11 is in the set.
    constructor 
    · -- 11 is prime 
      norm_num
    · -- Show 5 * 11^2 + 11^3 is a square.
      native_decide
  · -- Show that 11 is the least in the set
    intro p hp 
    rcases hp with ⟨h_prime, h_is_sq⟩
    by_contra h
    push_neg at h
    have h1 : p < 11 := h
    interval_cases p <;> try { 
      norm_num at h_prime h_is_sq 
      <;> try { 
        contrapose! h_is_sq 
        native_decide 
      } 
    }