import Mathlib

theorem number_theory_172484 (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≤ y) (hyz : y ≤ z) :
    (1 + 1 / x : ℚ) * (1 + 1 / y : ℚ) * (1 + 1 / z : ℚ) = 3 ↔
    (x = 1 ∧ y = 3 ∧ z = 8) ∨ (x = 1 ∧ y = 4 ∧ z = 5) ∨ (x = 2 ∧ y = 2 ∧ z = 3) := by
  constructor
  · -- Forward implication: if the equation holds, prove the possible triples
    intro h_eq
    have h1 : (x : ℚ) > 0 := by exact_mod_cast hx
    have h2 : (y : ℚ) > 0 := by exact_mod_cast hy
    have h3 : (z : ℚ) > 0 := by exact_mod_cast hz
    have eq1 : (x + 1 : ℚ) * (y + 1 : ℚ) * (z + 1 : ℚ) = 3 * ((x : ℚ) * (y : ℚ) * (z : ℚ)) := by 
      have h_eq' : (1 + 1 / x : ℚ) * (1 + 1 / y : ℚ) * (1 + 1 / z : ℚ) = 3 := h_eq
      field_simp at h_eq' ⊢
      nlinarith
    have eq2 : (x + 1 : ℤ) * (y + 1 : ℤ) * (z + 1 : ℤ) = 3 * ((x : ℤ) * (y : ℤ) * (z : ℤ)) := by
      exact_mod_cast eq1
    have h2' : x ≤ 2 := by
      nlinarith [sq_nonneg ((x : ℤ) - 2 : ℤ), sq_nonneg ((y : ℤ) - (x : ℤ)), sq_nonneg ((z : ℤ) - (y : ℤ)), 
          mul_nonneg (show (0 : ℤ) ≤ (y : ℤ) by positivity) (show (0 : ℤ) ≤ (z : ℤ) by positivity), 
          mul_nonneg (show (0 : ℤ) ≤ (x : ℤ) by positivity) (show (0 : ℤ) ≤ (y : ℤ) by positivity)
        ]
    have h3' : x = 1 ∨ x = 2 := by 
      omega
    rcases h3' with h3' | h3'
    · -- x = 1
      have eq3 : (x : ℤ) = 1 := by
        omega
      rw [eq3] at eq2
      have h4 : (y : ℤ) ≤ 8 := by
        nlinarith [sq_nonneg ((y : ℤ) - 8 : ℤ), sq_nonneg ((z : ℤ) - (y : ℤ)), 
            mul_nonneg (show (0 : ℤ) ≤ (y : ℤ) by positivity) (show (0 : ℤ) ≤ (z : ℤ) by positivity)
          ]
      have h4' : y ≤ 8 := by 
        omega
      interval_cases y <;> try { 
        omega 
      }
    · -- x = 2
      have eq3 : (x : ℤ) = 2 := by 
        omega
      rw [eq3] at eq2
      have h4 : (y : ℤ) ≤ 5 := by
        nlinarith [sq_nonneg ((y : ℤ) - 5 : ℤ), sq_nonneg ((z : ℤ) - (y : ℤ)), 
            mul_nonneg (show (0 : ℤ) ≤ (y : ℤ) by positivity) (show (0 : ℤ) ≤ (z : ℤ) by positivity)
          ]
      have h4' : y ≤ 5 := by 
        omega
      interval_cases y <;> try { 
        omega 
      }
  · -- Backward: if the triples are given, prove the equation
    rintro (h | h | h)
    · -- (1, 3, 8)
      rcases h with ⟨rfl, rfl, rfl⟩
      norm_num
    · -- (1, 4, 5)
      rcases h with ⟨rfl, rfl, rfl⟩
      norm_num
    · -- (2, 2, 3)
      rcases h with ⟨rfl, rfl, rfl⟩
      norm_num