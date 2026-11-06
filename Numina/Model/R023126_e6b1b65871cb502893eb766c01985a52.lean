import Mathlib

theorem algebra_277411 :
    Set.ncard {p : ℤ × ℤ | p.1 < p.2 ∧ p.1 + p.2 < 100 ∧ (p.1 : ℝ) / 4 + (p.2 : ℝ) / 10 = 7} = 19 := by 
  have h1 : {p : ℤ × ℤ | p.1 < p.2 ∧ p.1 + p.2 < 100 ∧ (p.1 : ℝ) / 4 + (p.2 : ℝ) / 10 = 7} = 
    Finset.filter (fun p : ℤ × ℤ => p.1 < p.2 ∧ p.1 + p.2 < 100 ∧ 5 * p.1 + 2 * p.2 = 140) 
      (Finset.Icc (-40 : ℤ) 40 ×ˢ Finset.Icc (-40 : ℤ) 140) := by 
    ext ⟨a, b⟩
    simp
    constructor
    · -- Assume (a, b) satisfy the three conditions
      rintro ⟨h1, h2, h3⟩
      have h4 : (a : ℝ) / 4 + (b : ℝ) / 10 = 7 := by
        simpa using h3
      have h5 : 5 * (a : ℝ) + 2 * (b : ℝ) = 140 := by 
        have h6 : (a : ℝ) / 4 + (b : ℝ) / 10 = 7 := h4
        linarith
      have h6 : 5 * a + 2 * b = 140 := by 
        exact_mod_cast h5
      omega 
    · -- Assume (a, b) is in the Finset 
      rintro ⟨h1, h2, h3⟩ 
      have h4 : 5 * a + 2 * b = 140 := by 
        omega 
      have h5 : (a : ℝ) / 4 + (b : ℝ) / 10 = 7 := by 
        have h6 : 5 * a + 2 * b = 140 := h4 
        have h7 : 5 * (a : ℝ) + 2 * (b : ℝ) = 140 := by 
          exact_mod_cast h6 
        linarith 
      constructor 
      · linarith 
      constructor 
      · linarith
      · simpa using h5
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide