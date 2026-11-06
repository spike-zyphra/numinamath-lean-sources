import Mathlib

theorem algebra_173023 {x : ℝ} (A B : Finset ℝ)
    (hA : A = {x^2, x + 1, -3}) (hB : B = {x - 5, 2 * x - 1, x^2 + 1})
    (hAB : A ∩ B = {-3}) : x = -1 := by 
  have h1 : -3 ∈ A ∩ B := by
    simp [hAB]
  have h3 : -3 ∈ A := by 
    simp [hA]
  have h4 : -3 ∈ B := by 
    simp [hA, hB] at h1 ⊢
    all_goals tauto
  have h4' : (x - 5 = -3) ∨ (2 * x - 1 = -3) ∨ (x^2 + 1 = -3) := by
    simp [hB] at h4 
    norm_num at h4 ⊢
    tauto
  rcases h4' with (h | h | h)
  · -- Assume x -5 = -3
    have hx : x = 2 := by 
      linarith 
    rw [hA, hB, hx] at hAB 
    norm_num [Finset.ext_iff] at hAB 
    all_goals linarith 
  · -- Assume 2x - 1 = -3 
    have hx : x = -1 := by 
      linarith 
    linarith 
  · -- Assume x^2 +1 = -3 
    nlinarith [sq_nonneg x]