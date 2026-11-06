import Mathlib

theorem algebra_328167 {a b c : ℝ} (ha : a ≠ 0) (x : ℕ → ℝ)
    (hx : ∀ i ∈ Finset.range 7, x (i + 1) = x i + (x 1 - x 0)) :
    a * x 0 ^ 2 + b * x 0 + c = 51 ∧
    a * x 1 ^ 2 + b * x 1 + c = 107 ∧
    a * x 2 ^ 2 + b * x 2 + c = 185 ∧
    a * x 3 ^ 2 + b * x 3 + c = 285 ∧
    a * x 4 ^ 2 + b * x 4 + c = 407 ∧
    a * x 5 ^ 2 + b * x 5 + c = 549 ∧
    a * x 6 ^ 2 + b * x 6 + c = 717 →
    a * x 3 ^ 2 + b * x 3 + c = 551 := by 
  intro h
  rcases h with ⟨eq0, eq1, eq2, eq3, eq4, eq5, eq6⟩

  have h1 : x 1 = x 0 + (x 1 - x 0) := by
    specialize hx 0 (by simp)
    simpa using hx

  have h2 : x 2 = x 1 + (x 1 - x 0) := by
    specialize hx 1 (by simp)
    simpa using hx

  have h3 : x 3 = x 2 + (x 1 - x 0) := by
    specialize hx 2 (by simp)
    simpa using hx

  have h4 : x 4 = x 3 + (x 1 - x 0) := by
    specialize hx 3 (by simp)
    simpa using hx

  have h5 : x 5 = x 4 + (x 1 - x 0) := by
    specialize hx 4 (by simp)
    simpa using hx

  have h6 : x 6 = x 5 + (x 1 - x 0) := by
    specialize hx 5 (by simp)
    simpa using hx

  have eq3' : x 3 = 3 * x 1 - 2 * x 0 := by
    linarith [h1, h2, h3]

  have eq4' : x 4 = 4 * x 1 - 3 * x 0 := by 
    linarith [h1, h2, h3, h4]

  have eq5' : x 5 = 5 * x 1 - 4 * x 0 := by
    linarith [h1, h2, h3, h4, h5]

  have eq6' : x 6 = 6 * x 1 - 5 * x 0 := by 
    linarith [h1, h2, h3, h4, h5, h6]

  have eq2' : x 2 = 2 * x 1 - x 0 := by
    linarith [h1, h2]

  rw [eq2'] at eq2 
  rw [eq3'] at eq3 
  rw [eq4'] at eq4 
  rw [eq5'] at eq5 
  rw [eq6'] at eq6

  nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact ha), sq_nonneg (x 0 - 1), sq_nonneg (x 1 - 2), sq_nonneg (b - 2), sq_nonneg (a - 4)]