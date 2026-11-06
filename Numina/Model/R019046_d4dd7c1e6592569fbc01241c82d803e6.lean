import Mathlib

open Real
open scoped BigOperators

/- sis: *Take $n(\geqslant 2)$ distinct fractions in the interval $(0,1)$. Prove: the sum of the denominators of these fractions is not less than $\frac{1}{3} n^{\frac{3}{2}}$. -/
theorem number_theory_119486 {n : ℕ} (hn : 2 ≤ n) (s : Finset ℚ)
  (h₀ : ∀ x ∈ s, 0 < x ∧ x < 1) (h₁ : s.card = n) :
  ∑ x ∈ s, x.den ≥ 1 / 3 * n ^ (3 / 2) := by 
  have h2 : ∀ x ∈ s, x.den ≥ 1 := by
    intro x hx
    have hx2 := (h₀ x hx).1
    have hx3 := (h₀ x hx).2
    have hxne0 : x ≠ 0 := by
      have : x > 0 := hx2
      have : x > (0 : ℚ) := by exact_mod_cast hx2
      linarith
    have hxne1 : x ≠ 1 := by
      have : x < 1 := hx3
      have : x < (1 : ℚ) := by exact_mod_cast hx3
      linarith
    have h5 : x.den ≥ 1 := by
      exact Nat.succ_le_of_lt (show 0 < x.den by
      -- Use the relationship between numerator and denominator
        by_contra h
        push_neg at h
        have h6 : x.den = 0 := by
          omega
        have h7 : x = (0 : ℚ) := by
          rw [show x = (x.num : ℤ) / (x.den : ℤ) by 
            field_simp [Rat.num_div_den]
          ] -- standard representation
          rw [h6]
          norm_num
          <;> norm_num at *
          <;> norm_num
          <;> tauto
        contradiction)
    exact h5
  have h3 : ∑ x in s, x.den ≥ ∑ x in s, (1 : ℕ) := by
    apply Finset.sum_le_sum
    intro x hx
    exact_mod_cast h2 x hx
  have h4 : ∑ x in s, (1 : ℕ) = n := by 
    simp [h₁]
  rw [h4] at h3
  have h5 : n ≥ 2 := hn
  have h6 : 1 / 3 * n ^ (3 / 2) ≤ (n : ℕ) := by 
    have h7 : n ≥ 2 := h5
    have h8 : n ^ (3 / 2) ≤ 3 * n := by 
      have h81 : n ^ (3 / 2) ≤ 3 * n := by 
        norm_num
        all_goals nlinarith
      omega
    have h9 : 1 / 3 * n ^ (3 / 2) ≤ n := by 
      omega
    omega
  omega