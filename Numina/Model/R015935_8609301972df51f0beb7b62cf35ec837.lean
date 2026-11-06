import Mathlib

theorem algebra_138158 {G : Type*} [Group G] (x y z : G)
    (h1 : x * y = 1) (h2 : z * x = 1) :
    y = z ∧ z = x⁻¹ := by
  have h3 : y = z := by
    have eq1 : x * y = 1 := h1
    have eq2 : z * x = 1 := h2
    have h4 : z * (x * y) = z := by 
      calc
        z * (x * y) = z * (1 : G) := by rw [show x * y = 1 by exact eq1]
        _ = z := by simp
    have h8 : (z * x) * y = z := by 
      have h7 : (z * x) * y = z * (x * y) := by 
        rw [mul_assoc]
      rw [h7]
      exact h4
    have h11 : 1 * y = z := by
      have h9 : (z * x) * y = 1 * y := by 
        have h6 : z * x = 1 := h2
        rw [h6]
      rw [h9] at h8
      exact h8
    have h13 : y = z := by 
      simp at h11 ⊢
      all_goals try tauto
    exact h13
  have h10 : z = x⁻¹ := by
    have h11 : x * z = 1 := by 
      have h12 : x * y = 1 := h1
      have h13 : y = z := h3
      rw [show y = z by exact h13] at h12
      all_goals 
        try tauto
    have h12 : z = x⁻¹ := by
      have h13 : x * z = 1 := h11
      have h14 : z = x⁻¹ := by 
        have h15 : z = x⁻¹ := by
          have h16 : x * z = 1 := h13
          have h17 : z = x⁻¹ := by
            -- a * b = 1 → b = a⁻¹
            have h18 : x * z = 1 := h16
            have h19 : z = x⁻¹ := by
              have h19 : x * z = 1 := h18
              exact eq_inv_of_mul_eq_one_right h19
            exact h19
          exact h17
        exact h15
      exact h14
    exact h12
  constructor
  · exact h3
  · exact h10