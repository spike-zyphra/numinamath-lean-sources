import Mathlib

theorem inequalities_78960 (u v : ℝ) (a b : ℝ) (h₀ : 0 ≤ u) (h₁ : 0 ≤ v)
    (h₂ : 0 < a) (h₃ : 0 < b) (h₄ : a + b = 1) :
    u ^ a * v ^ b ≤ a * u + b * v := by
  have h5 : b = 1 - a := by linarith
  have h7 : u ^ a * v ^ b ≤ a * u + b * v := by
    have h8 : a + b = 1 := h₄
    have h67 : u ^ a * v ^ b ≤ a * u + b * v := by
      have h123 : u ^ a * v ^ b ≤ a * u + (1 - a) * v := by
        have h7' : 0 ≤ 1 - a := by linarith
        have h8' : a + (1 - a) = 1 := by linarith
        have h9 : u ^ a * v ^ (1 - a) ≤ a * u + (1 - a) * v := by
          apply Real.geom_mean_le_arith_mean2_weighted
          all_goals
            try linarith
            try positivity
        have h7_eq' : v ^ b = v ^ (1 - a) := by 
          rw [show b = 1 - a by linarith]
        have h123_eq : u ^ a * v ^ b = u ^ a * v ^ (1 - a) := by 
          rw [h7_eq']
        rw [h123_eq] at *
        linarith
      have h67_eq :  a * u + b * v = a * u + (1 - a) * v := by 
        rw [show b = 1 - a by linarith]
      have h123_eq : a * u + b * v = a * u + (1 - a) * v := by 
        rw [show b = 1 - a by linarith]
      linarith [h123,h123_eq]
      <;> linarith
    exact h67
  exact h7