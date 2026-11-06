import Mathlib

theorem algebra_189132 {f : ℝ → ℝ} (hf : ∀ x, x ≠ 2 → f x = x * f ((2 * x + 3) / (x - 2)) + 3)
    (hf2 : f 2 = 0) :
    ∀ x, f x = 3 * (x + 1) * (2 - x) / (2 * (x ^ 2 + x + 1)) := by
  intro x
  by_cases h : x = 2
  · -- x = 2.
    rw [h]
    rw [hf2]
    norm_num
  · -- x ≠ 2.
    have hx : x ≠ 2 := h
    have eq1' : f x = x * f ((2 * x + 3) / (x - 2)) + 3 := by
      apply hf x
      exact hx
    have eq5 : f ((2 * x + 3) / (x - 2)) = ((2 * x + 3) / (x - 2)) * f x + 3 := by
      have h4' : ((2 * ((2 * x + 3) / (x - 2)) + 3) / (((2 * x + 3) / (x - 2)) - 2)) = x := by
        have h1 : x - 2 ≠ 0 := by
          intro h'
          apply hx
          linarith
        have h4 : (2 * ((2 * x + 3) / (x - 2)) + 3) = 7 * x / (x - 2) := by
          field_simp [(show x - 2 ≠ 0 by exact h1)]
          ring
        have h5 : ((2 * x + 3) / (x - 2)) - 2 = 7 / (x - 2) := by
          field_simp [(show x - 2 ≠ 0 by exact h1)]
          ring
        rw [h4, h5]
        have h7 : x - 2 ≠ 0 := h1
        field_simp [h7]
        <;> ring
      have eq3' : f ((2 * x + 3) / (x - 2)) = ((2 * x + 3) / (x - 2)) * f ((2 * ((2 * x + 3) / (x - 2)) + 3) / (((2 * x + 3) / (x - 2)) - 2)) + 3 := by
        have h1 : ((2 * x + 3) / (x - 2)) ≠ 2 := by
          apply (show ((2 * x + 3) / (x - 2)) ≠ 2 by
            by_contra h
            have h1 : x - 2 ≠ 0 := by
              intro h1
              apply hx
              linarith
            have h7 : (2 * x + 3) = 2 * (x - 2) := by
              field_simp [(show x - 2 ≠ 0 by exact h1)] at h ⊢
              linarith
            nlinarith
          )
        apply hf ((2 * x + 3) / (x - 2)) h1
      rw [h4'] at eq3'
      linarith
    rw [eq5] at eq1'
    have eq7 : f x = x * (( (2 * x + 3) / (x - 2) ) * f x + 3 ) + 3 := by
      linarith
    have eq8 : f x = (3 * (x + 1) * (2 - x)) / (2 * (x ^ 2 + x + 1)) := by
      have hx1 : x - 2 ≠ 0 := by
        intro h'
        apply hx
        linarith
      have h9 : (x^2 + x + 1) ≠ 0 := by
        have h10 : x^2 + x + 1 > 0 := by
          nlinarith [sq_nonneg (x + 1 / 2)]
        nlinarith
      have eq7' : f x * (1 - x * ((2 * x + 3) / (x - 2))) = 3 * x + 3 := by
        linarith
      have eq9 : (1 - x * ((2 * x + 3) / (x - 2))) = (-2 * (x ^ 2 + x + 1)) / (x - 2) := by
        field_simp [(show x - 2 ≠ 0 by exact hx1)]
        ring
      rw [eq9] at eq7'
      have h5 : (x - 2) ≠ 0 := by 
        intro h
        apply hx
        linarith
      have h2 : x ^ 2 + x + 1 ≠ 0 := by
        have h10 : x ^ 2 + x + 1 > 0 := by
          nlinarith [sq_nonneg (x + 1 / 2)]
        nlinarith
      have eq19 : f x = (3 * (x + 1) * (2 - x)) / (2 * (x ^ 2 + x + 1)) := by
        field_simp [(show x - 2 ≠ 0 by exact hx1), (show x^2 + x + 1 ≠ 0 by exact h2)] at eq7' ⊢
        nlinarith [sq_pos_of_ne_zero (show x ^ 2 + x + 1 ≠ 0 by exact h2)]
      linarith
    linarith [eq8]