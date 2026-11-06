import Mathlib

theorem algebra_242717 {x y z : ℝ} (h₀ : x^2 = (y - z)^2 - 8) (h₁ : y^2 = (z - x)^2 - 20)
    (h₂ : z^2 = (x - y)^2 + 40) :
    (x = -1 ∧ y = -4 ∧ z = -7) ∨ (x = 1 ∧ y = 4 ∧ z = 7) := by 
  have eq1 : x^2 = y^2 - 2 * y * z + z^2 - 8 := by linarith [h₀]
  have eq2 : y^2 = z^2 - 2 * z * x + x^2 - 20 := by linarith [h₁]
  have eq3 : z^2 = x^2 - 2 * x * y + y^2 + 40 := by linarith [h₂]
  have eq4 : (x + 1) * (x - 1) = 0 := by nlinarith
  have eq5 : (y + 4) * (y - 4) = 0 := by nlinarith
  have eq6 : (z + 7) * (z - 7) = 0 := by nlinarith
  cases' (mul_eq_zero.1 eq4) with h3 h4
  · -- Case x = -1
    have hx : x = -1 := by linarith
    cases' (mul_eq_zero.1 eq5) with h5 h6
    · -- Case y = -4
      have hy : y = -4 := by linarith
      -- Now, solving for z
      have h7 : z = -7 := by
        nlinarith [h₀, h₁, h₂, hx, hy]
      left
      exact ⟨by linarith, by linarith, by linarith⟩
    · -- Case y = 4
      have hy : y = 4 := by linarith
      -- Now, solving for z
      exfalso
      nlinarith [h₀, h₁, h₂, hx, hy]
  · -- Case x = 1
    have hx : x = 1 := by linarith
    cases' (mul_eq_zero.1 eq5) with h5 h6
    · -- Case y = -4
      have hy : y = -4 := by linarith
      -- Now, solving for z
      exfalso
      nlinarith [h₀, h₁, h₂, hx, hy]
    · -- Case y = 4
      have hy : y = 4 := by linarith
      -- Now, solving for z
      have h7 : z = 7 := by
        nlinarith [h₀, h₁, h₂, hx, hy]
      right
      exact ⟨by linarith, by linarith, by linarith⟩