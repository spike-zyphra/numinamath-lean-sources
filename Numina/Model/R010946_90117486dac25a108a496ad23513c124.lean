import Mathlib

theorem algebra_202124 {x y z a : ℝ} (h₀ : x + y + z = a) (h₁ : 1 / x + 1 / y + 1 / z = 1 / a) (h₂ : x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ a ≠ 0) :
    x = a ∨ y = a ∨ z = a := by
  rcases h₂ with ⟨hx, hy, hz, ha⟩
  have h3 : x ≠ 0 := hx
  have h4 : y ≠ 0 := hy
  have h5 : z ≠ 0 := hz
  have h6 : a ≠ 0 := ha
  have eq1 : (1 / x + 1 / y + 1 / z) * (x * y * z * a) = (1 / a) * (x * y * z * a) := by 
    rw [h₁]
  have eq2 : (1 / x + 1 / y + 1 / z) * (x * y * z * a) = y * z * a + x * z * a + x * y * a := by 
    field_simp [show x ≠ 0 by exact h3, show y ≠ 0 by exact h4, show z ≠ 0 by exact h5, show a ≠ 0 by exact h6]
    ring
  have eq3 : (1 / a) * (x * y * z * a) = x * y * z := by 
    field_simp [show a ≠ 0 by exact h6, show x ≠ 0 by exact h3, show y ≠ 0 by exact h4, show z ≠ 0 by exact h5]
    <;> ring
  rw [eq2, eq3] at eq1 
  have eq5 : y * z * a + x * z * a + x * y * a = x * y * z := by
    linarith [eq1]
  have eq6 : (x - a) * (y - a) * (z - a) = 0 := by
    have eq7 : a = x + y + z := by 
      linarith 
    rw [show a = x + y + z by linarith] at eq5 
    have eq8 : (x - a) * (y - a) * (z - a) = 0 := by
      have eq9 : y * z * (x + y + z) + x * z * (x + y + z) + x * y * (x + y + z) = x * y * z := by 
        linarith
      have eq10 : (x - (x + y + z)) * (y - (x + y + z)) * (z - (x + y + z)) = 0 := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), 
          sq_pos_of_ne_zero (show x ≠ 0 by exact h3), 
          sq_pos_of_ne_zero (show y ≠ 0 by exact h4), 
          sq_pos_of_ne_zero (show z ≠ 0 by exact h5), 
          sq_pos_of_ne_zero (show a ≠ 0 by exact h6)
        ]
      have : (x - a) * (y - a) * (z - a) = (x - (x + y + z)) * (y - (x + y + z)) * (z - (x + y + z)) := by
        have h5 : a = x + y + z := by linarith
        rw [h5]
      nlinarith
    linarith 
  cases' (mul_eq_zero.mp eq6) with h7 h8
  cases' (mul_eq_zero.mp h7) with h9 h10
  · -- Case where (x - a) = 0 
    left 
    linarith 
  · -- Case where (y - a) = 0 
    right 
    left 
    linarith 
  · -- Case where (z - a) = 0 
    right 
    right 
    linarith