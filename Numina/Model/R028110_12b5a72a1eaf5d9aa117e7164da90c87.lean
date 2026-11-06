import Mathlib

theorem algebra_325177 (x : ℝ) (hx : 6*x-5≠0 ∧ 5*x+4≠0 ∧ 5*x-4≠0 ∧ 4*x+5≠0) :
    1/(6*x-5) - 1/(5*x+4) = 1/(5*x-4) - 1/(4*x+5) ↔ x=9 ∨ x=0 ∨ x=1 := by 
  rcases hx with ⟨hx1, hx2, hx3, hx4⟩
  constructor
  · -- Assume the equation, prove the three solutions.
    intro h
    have eq1 : 1/(6*x-5) - 1/(5*x+4) = (-x+9)/((6*x-5)*(5*x+4)) := by 
      field_simp [hx1, hx2]
      <;> ring_nf 
    have eq2 : 1/(5*x-4) - 1/(4*x+5) = (-x+9)/((5*x-4)*(4*x+5)) := by 
      field_simp [hx3, hx4]
      <;> ring_nf 
    rw [eq1] at h
    rw [eq2] at h
    by_cases h4 : -x + 9 = 0
    · -- Case where $x = 9$.
      have hx9 : x = 9 := by 
        linarith 
      left 
      exact hx9 
    · -- Case where $-x + 9 ≠ 0$. 
      have eq5 : (5 * x - 4) * (4 * x + 5) = (6 * x - 5) * (5 * x + 4) := by 
        have h6 : (-x + 9) / ((6 * x - 5) * (5 * x + 4)) = (-x + 9) / ((5 * x - 4) * (4 * x + 5)) := h 
        have h4' : -x + 9 ≠ 0 := by
          by_contra h8
          have : -x + 9 = 0 := by 
            linarith
          contradiction
        have : (5 * x - 4) * (4 * x + 5) = (6 * x - 5) * (5 * x + 4) := by 
          field_simp [(show (6 * x - 5 : ℝ) ≠ 0 by assumption), 
            (show (5 * x + 4 : ℝ) ≠ 0 by assumption), 
            (show (5 * x - 4 : ℝ) ≠ 0 by assumption), 
            (show (4 * x + 5 : ℝ) ≠ 0 by assumption)] at h6
          have h7 : -x + 9 ≠ 0 := h4'
          have h8 : ((5 * x - 4) * (4 * x + 5) ) = ((6 * x - 5) * (5 * x + 4) ) := by 
            cases h6 with 
            | inl h1 => linarith 
            | inr h2 => 
              -- Derives contradiction if second part of hypothesis is true.
              exfalso 
              apply h7 
              linarith 
          assumption 
        assumption 
      have eq4 : 10 * x^2 - 10 * x = 0 := by 
        nlinarith [eq5]
      have eq6 : 10 * x * (x - 1) = 0 := by 
        linarith [eq4] 
      cases' (mul_eq_zero.mp eq6) with eq7 eq8 
      · -- When $10 * x = 0$, so $x = 0$.
        have hx0 : x = 0 := by 
          linarith 
        right 
        left 
        exact hx0 
      · -- When $x - 1 = 0$, so $x = 1$.
        have hx1 : x = 1 := by 
          linarith 
        right 
        right 
        exact hx1 
  · -- Backward implication
    rintro (h | h | h)
    · -- Assume x = 9.
      rw [h]
      norm_num
    · -- Assume x = 0.
      rw [h]
      norm_num
    · -- Assume x = 1.
      rw [h]
      norm_num