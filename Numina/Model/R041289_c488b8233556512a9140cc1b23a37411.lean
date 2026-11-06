import Mathlib

open Real

/-
Solve the following inequality:
$$
\sqrt{x+\sqrt{x}}-\sqrt{x-\sqrt{x}}>\frac{4}{3} \sqrt{\frac{x}{x+\sqrt{x}}}
$$
-/

-- We have to add hypotheses that all expressions inside square roots are nonnegative.
-- This is also explained / used in the Markdown solution.
-- Also, denominators have to be nonzero.
theorem inequalities_213788 (x : ℝ)
    (hx1 : 0 ≤ x) (hx2 : 0 < x + √x) (hx3 : 0 ≤ x - √x)
    (hx4 : 0 ≤ x / (x + √x)) :
    √(x + √x) - √(x - √x) > 4 / 3 * √(x / (x + √x)) → 1 ≤ x ∧ x < 25 / 9 := by 
  intro h
  have h1 : 1 ≤ x := by
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg (x + Real.sqrt x), Real.sqrt_nonneg (x - Real.sqrt x), sq_nonneg (Real.sqrt x - 1), Real.sq_sqrt (show 0 ≤ x by linarith), Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith), Real.sqrt_nonneg (x / (x + Real.sqrt x)), h]

  have h2 : x < 25 / 9 := by
    have h3 : 0 ≤ x := by linarith
    have h4 : 0 ≤ √x := Real.sqrt_nonneg x
    have h5 : √x ^ 2 = x := Real.sq_sqrt (by linarith)
    have h6 : √(x / (x + √x)) = √x / √(x + √x) := by 
      have h7 : 0 < x + √x := hx2
      have h8 : √(x / (x + √x)) = √x / √(x + √x) := by 
        field_simp [Real.sqrt_div]
      exact h8 
    have h7 : √(x + √x) > 0 := by 
      apply Real.sqrt_pos.mpr
      linarith [show 0 < x + √x by exact hx2]
    have h8 : (√(x + √x) - √(x - √x)) > 4 / 3 * (√x / √(x + √x)) := by 
      rw [h6] at h 
      exact_mod_cast h 
    have h9 : (√(x + √x) - √(x - √x)) * √(x + √x) > (4 / 3 * (√x / √(x + √x))) * √(x + √x) := by 
      apply mul_lt_mul_of_pos_right h8 (by
        have h44 : 0 < √(x + √x) := h7 
        linarith 
      )
    have h10 : (4 / 3 * (√x / √(x + √x))) * √(x + √x) = 4 / 3 * √x := by
      field_simp [show √(x + √x) > 0 by exact h7]
      <;> nlinarith 
    have h11 : (√(x + √x) - √(x - √x)) * √(x + √x) = (√(x + √x) ^ 2) - (√(x - √x) * √(x + √x)) := by 
      ring 
    have h12 : (√(x + √x) ^ 2) = x + √x := by 
      rw [Real.sq_sqrt]
      nlinarith [show x + √x ≥ 0 by nlinarith [Real.sqrt_nonneg x]]
    have h13 : (√(x - √x) * √(x + √x)) = Real.sqrt (x ^ 2 - x) := by 
      have h13 : (√(x - √x) * √(x + √x)) = Real.sqrt ((x - √x) * (x + √x)) := by 
        rw [← Real.sqrt_mul (by 
          nlinarith [Real.sqrt_nonneg x, mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg x)]
        )]
      rw [h13]
      have : (x - √x) * (x + √x) = x ^ 2 - x := by 
        nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show 0 ≤ x by linarith)]
      rw [this]
    have h11' : (√(x + √x) - √(x - √x)) * √(x + √x) = x + √x - Real.sqrt (x ^ 2 - x) := by 
      rw [h11, h12, h13] 
      <;> nlinarith 
    rw [h11'] at h9 
    rw [h10] at h9 
    by_contra h14 
    push_neg at h14 
    have h10 : x ≥ 25 / 9 := h14 
    have h15 : Real.sqrt x ≥ 5 / 3 := by
      nlinarith [Real.sqrt_nonneg x, sq_nonneg (Real.sqrt x - 5 / 3), Real.sq_sqrt (show 0 ≤ x by linarith)]
    have h16 : x ^ 2 - x ≥ 0 := by
      nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show 0 ≤ x by linarith), h10]
    have h17 : Real.sqrt (x ^ 2 - x) ≥ 0 := by 
      apply Real.sqrt_nonneg 
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg (x + √x), Real.sqrt_nonneg (x - √x), Real.sq_sqrt (show 0 ≤ x by linarith), Real.sq_sqrt (show 0 ≤ x + √x by nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show 0 ≤ x by linarith)]), Real.sq_sqrt (show 0 ≤ x - √x by nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show 0 ≤ x by linarith)]), sq_nonneg (Real.sqrt x - 5 / 3), mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg x), Real.sq_sqrt (show x ^ 2 - x ≥ 0 by nlinarith)]
  
  exact ⟨h1, h2⟩