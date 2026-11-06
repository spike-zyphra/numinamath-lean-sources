import Mathlib

theorem algebra_175881 (p q : ℝ) (h : p^2 - 4 * q ≥ 0) :
    {x | x^2 + p * x + q = 0} = {-p / 2 + Real.sqrt ((p ^ 2) / 4 - q), -p / 2 - Real.sqrt ((p ^ 2) / 4 - q)} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Forward direction: if x^2 + px + q = 0, then x is one of the two roots
    intro hx
    have h1 : x^2 + p * x + q = 0 := hx
    have eq1 : (x + p / 2) ^ 2 = (p ^ 2) / 4 - q := by 
      nlinarith 
    have h2 : (Real.sqrt ((p ^ 2) / 4 - q)) ^ 2 = (p ^ 2) / 4 - q := by
      rw [Real.sq_sqrt]
      have h3 : ((p : ℝ) ^ 2) / 4 - q ≥ 0 := by
        linarith [h]
      exact h3 
    have h3 : (x + p / 2) ^ 2 = (Real.sqrt ((p ^ 2) / 4 - q)) ^ 2 := by linarith [eq1, h2]
    have h4 : (x + p / 2) = Real.sqrt ((p ^ 2) / 4 - q) ∨ (x + p / 2) = -Real.sqrt ((p ^ 2) / 4 - q) := by
      apply eq_or_eq_neg_of_sq_eq_sq 
      all_goals 
        nlinarith 
    cases h4 with
    | inl h5 =>
      left 
      linarith 
    | inr h6 =>
      right 
      linarith 
  · -- Backward direction: both roots satisfy the quadratic equation
    rintro (h | h)
    · -- Verify the first root
      rw [show x = -p / 2 + Real.sqrt ((p ^ 2)/4 - q) by linarith]
      nlinarith [Real.sqrt_nonneg ((p^2)/4 - q), Real.sq_sqrt (show (p^2)/4 - q ≥ 0 by linarith [h])]
    · -- Verify the second root
      rw [show x = -p / 2 - Real.sqrt ((p ^ 2)/4 - q) by linarith]
      nlinarith [Real.sqrt_nonneg ((p^2)/4 - q), Real.sq_sqrt (show (p^2)/4 - q ≥ 0 by linarith [h])]