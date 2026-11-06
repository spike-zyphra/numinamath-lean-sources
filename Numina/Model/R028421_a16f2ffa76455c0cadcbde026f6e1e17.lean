import Mathlib

theorem algebra_101084 {x : ℤ} (hx : ∃ n, x = n^2) :
    ∃ y, x + 2 * Real.sqrt x + 1 = y^2 := by
  rcases hx with ⟨n, hn⟩
  use (abs (n : ℝ) + 1 : ℝ)
  have h1 : (x : ℝ) = (n : ℝ) ^ 2 := by
    exact_mod_cast hn
  have h2 : Real.sqrt (x : ℝ) = abs (n : ℝ) := by
    rw [h1]
    rw [Real.sqrt_sq_eq_abs]
  have h3 : (x : ℝ) + 2 * Real.sqrt (x : ℝ) + 1 = ((abs (n : ℝ) + 1 : ℝ) ) ^ 2 := by
    rw [h2]
    have h4 : (x : ℝ) = (n : ℝ) ^ 2 := by
      exact_mod_cast hn
    rw [h4]
    have h5 : ((abs (n : ℝ) + 1 : ℝ)) ^ 2 = (abs (n : ℝ)) ^ 2 + 2 * abs (n : ℝ) + 1 := by
      ring
    have h6 : (abs (n : ℝ) ) ^ 2 = (n : ℝ) ^ 2 := by
      have h7 : abs (n : ℝ) ^ 2 = (n : ℝ) ^ 2 := by
        rw [sq_abs]
      linarith
    rw [h5, h6]
    all_goals
      nlinarith
  norm_num at h3 ⊢
  <;> nlinarith