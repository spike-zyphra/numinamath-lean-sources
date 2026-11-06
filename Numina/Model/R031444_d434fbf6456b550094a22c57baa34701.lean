import Mathlib

theorem algebra_1199 (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    (1 / a : ℚ) + (1 / b : ℚ) = 1 / 3 ↔ (a = 4 ∧ b = 12) ∨ (a = 6 ∧ b = 6) ∨ (a = 12 ∧ b = 4) := by
  constructor
  · -- Assume the equation holds, prove the disjunction 
    intro h 
    have h1 : (a : ℚ) > 0 := by exact_mod_cast ha 
    have h2 : (b : ℚ) > 0 := by exact_mod_cast hb
    have h3 : (a * b : ℚ) = 3 * (a + b : ℚ) := by 
      field_simp [(show (a : ℚ) ≠ 0 by positivity), (show (b : ℚ) ≠ 0 by positivity)] at h ⊢ 
      nlinarith
    have h4 : (a * b : ℤ) = 3 * (a + b : ℤ) := by
      exact_mod_cast h3
    have h5 : a * b = 3 * (a + b) := by 
      linarith 
    have h6 : a ≤ 12 := by
      by_contra h7 
      push_neg at h7 
      have h8 : b < 4 := by
        nlinarith [show 0 < a from ha, show 0 < b from hb, h5, h7]
      interval_cases b <;> try { 
        nlinarith 
      }
    have h7 : b ≤ 12 := by
      by_contra h8 
      push_neg at h8 
      have h9 : a < 4 := by
        nlinarith [show 0 < a from ha, show 0 < b from hb, h5, h8]
      interval_cases a <;> try { 
        nlinarith 
      }
    interval_cases a <;> try { 
      omega 
    }
  · -- Assume the disjunction holds, prove the equation 
    rintro (h | h | h)
    · -- First solution 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- Second solution 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- Third solution 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num