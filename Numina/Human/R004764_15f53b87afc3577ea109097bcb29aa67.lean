import Mathlib
/-Given that x1,...xn,where xi can only take one the values -2
0 1 and satisfy x1+ ...+xn = -17, x1^2+ ... +xn^2 = 37, then (x1^3+...+xn^3)^2 is ?-/
theorem algebra_318707 {n : ℕ} (x : Fin n → ℤ)
    (h1 : ∀ i, x i = -2 ∨ x i = 0 ∨ x i = 1)
    (h2 : ∑ i, x i = -17) (h3 : ∑ i, (x i)^2 = 37) :
    (∑ i, (x i)^3)^2 = 5041 := by
  --first evaluate without square 
    have h_sum_eq : ∑ i, (x i) ^ 3 = -71 := by
     -- simplify the term
      have h17 : ∀ i, (x i) ^ 3 = - (x i) ^ 2 + 2 * (x i) := by
        intro i
        have h18 : (x i) = -2 ∨ (x i) = 0 ∨ (x i) = 1 := h1 i
        rcases h18 with (h18 | h18 | h18)
        · -- x i = -2 
          rw [h18]
          norm_num
        · -- x i = 0 
          rw [h18]
          norm_num
        · -- x i = 1 
          rw [h18]
          norm_num
      -- plug the term in terms of square and one pow
      have h19 : ∑ i, (x i) ^ 3 = - ∑ i, (x i) ^ 2 + 2 * ∑ i, (x i) := by 
        calc 
          ∑ i, (x i) ^ 3 = ∑ i, (- (x i) ^ 2 + 2 * (x i)) := by 
            congr 
            funext i 
            exact h17 i
          _ = - ∑ i, (x i) ^ 2 + 2 * ∑ i, (x i) := by 
            rw [Finset.sum_add_distrib]
            rw [← Finset.mul_sum]
            simp [Finset.sum_neg_distrib]
      rw [h3, h2] at h19
      linarith 
    calc 
      (∑ i, (x i) ^ 3) ^ 2 = (-71) ^ 2 := by rw [h_sum_eq]
      _ = 5041 := by norm_num