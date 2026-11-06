import Mathlib

open Real
open scoped BigOperators

theorem algebra_2102 :
  Set.ncard {n : ℤ | ∃ x : ℝ, n = (4 * x ^ 2 + 75) / (2 * x ^ 2 + 3)} = 23 := by
  have h1 : {n : ℤ | ∃ x : ℝ, n = (4 * x ^ 2 + 75) / (2 * x ^ 2 + 3)} = Set.Icc 3 25 := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- Assume there exists an x such that n = (4 * x ^ 2 + 75) / (2 * x ^ 2 + 3), prove 3 ≤ n ≤ 25.
      rintro ⟨x, hx⟩
      have h2 : (n : ℝ) = (4 * x ^ 2 + 75) / (2 * x ^ 2 + 3) := by
        simpa using hx
      have h3 : 0 < (2 * x ^ 2 + 3 : ℝ) := by
        nlinarith [sq_nonneg x]
      have eq1 : (4 * x ^ 2 + 75 : ℝ) = (n : ℝ) * (2 * x ^ 2 + 3) := by
        field_simp [(show (2 * x ^ 2 + 3 : ℝ) ≠ 0 by linarith [h3])] at h2 ⊢
        nlinarith
      have h4 : (n : ℝ) > (2 : ℝ) := by
        nlinarith [sq_nonneg x, sq_nonneg (x ^ 2), h3]
      have h5 : (n : ℝ) ≤ (25 : ℝ) := by
        nlinarith [sq_nonneg x, sq_nonneg (x ^ 2), h3]
      have h6 : n ≥ 3 := by
        by_contra h
        push_neg at h
        have : n ≤ 2 := by omega
        have hn : (n : ℝ) ≤ (2 : ℝ) := by exact_mod_cast this
        linarith
      have h7 : n ≤ 25 := by
        by_contra h
        push_neg at h
        have : n ≥ 26 := by omega
        have hn : (n : ℝ) ≥ (26 : ℝ) := by exact_mod_cast this
        linarith
      constructor
      · exact h6
      · exact h7
    · -- Assume 3 ≤ n ≤ 25, prove there exists an x such that n = (4 * x ^ 2 + 75) / (2 * x ^ 2 + 3).
      rintro ⟨hn1, hn2⟩
      have hn3 : n ≥ 3 := by omega
      have hn4 : n ≤ 25 := by omega
      have hn5 : (n : ℝ) ≥ (3 : ℝ) := by exact_mod_cast hn3
      have hn6 : (n : ℝ) ≤ (25 : ℝ) := by exact_mod_cast hn4
      have h7 : (2 * (n : ℝ) - 4 : ℝ) > 0 := by
        have hn3 : (n : ℝ) ≥ (3 : ℝ) := by exact_mod_cast hn3
        nlinarith
      have h8 : (75 - 3 * (n : ℝ)) / (2 * (n : ℝ) - 4) ≥ (0 : ℝ) := by
        apply div_nonneg
        · -- Show that numerator is non-negative
          have hn7 : (n : ℝ) ≤ (25 : ℝ) := by exact_mod_cast hn4
          nlinarith
        all_goals -- Show that denominator is non-negative
          have h9 : (2 * (n : ℝ) - 4 : ℝ) > (0 : ℝ) := by
            have hn3 : (n : ℝ) ≥ (3 : ℝ) := by exact_mod_cast hn3
            nlinarith
          nlinarith
      use - Real.sqrt ((75 - 3 * (n : ℝ)) / (2 * (n : ℝ) - 4))
      have h9 : (- Real.sqrt ((75 - 3 * (n : ℝ)) / (2 * (n : ℝ) - 4)) ) ^ 2 = (75 - 3 * (n : ℝ)) / (2 * (n : ℝ) - 4) := by
        have h10 : (75 - 3 * (n : ℝ)) / (2 * (n : ℝ) - 4) ≥ 0 := h8
        rw [neg_sq]
        rw [Real.sq_sqrt]
        linarith
      have eq2 : (4 * (- Real.sqrt ((75 - 3 * (n : ℝ)) / (2 * (n : ℝ) - 4)) ) ^ 2 + 75) / (2 * (- Real.sqrt ((75 - 3 * (n : ℝ)) / (2 * (n : ℝ) - 4)) ) ^ 2 + 3) = (n : ℝ) := by
        have hx2 : (- Real.sqrt ((75 - 3 * (n : ℝ)) / (2 * (n : ℝ) - 4) ) )^2 = (75 - 3 * (n : ℝ)) / (2 * (n : ℝ) - 4) := h9
        have hx2' : (4 * (- Real.sqrt ((75 - 3 * (n : ℝ)) / (2 * (n : ℝ) - 4)) ) ^ 2 + 75) = (138 * (n : ℝ)) / (2 * (n : ℝ) - 4) := by
          rw [h9]
          field_simp [(show (2 * (n : ℝ) - 4 : ℝ) ≠ 0 by linarith)]
          <;> 
            ring
        have hx2'' : (2 * (- Real.sqrt ((75 - 3 * (n : ℝ)) / (2 * (n : ℝ) - 4)) ) ^ 2 + 3) = (138 : ℝ) / (2 * (n : ℝ) - 4) := by 
          rw [h9]
          field_simp [(show (2 * (n : ℝ) - 4 : ℝ) ≠ 0 by linarith)]
          <;> 
            ring
        rw [hx2', hx2'']
        have h14 : (2 * (n : ℝ) - 4 : ℝ) ≠ 0 := by
          nlinarith
        field_simp [h14]
        <;> 
          ring
      linarith [eq2]
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> try native_decide