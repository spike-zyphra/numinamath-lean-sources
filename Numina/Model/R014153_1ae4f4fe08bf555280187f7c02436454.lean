import Mathlib

theorem algebra_12293 {p : ℝ → ℝ}
    (hp : ∀ x, p x = if x ∈ Set.Icc (-3.5) 3.5 then (Real.sign (2 * x - 2)) * (abs (2 * x - 2)) ^ ((1 : ℝ) / 3) +
      2 * (Real.sign (2 * x - 2)) * (abs (2 * x - 2)) ^ ((1 : ℝ) / 5) +
      (abs (2 * x - 2)) ^ ((1 : ℝ) / 7) else 0) :
    p 1.5 = 4 := by
  have h1 : p 1.5 = (Real.sign (2 * (1.5 : ℝ) - 2)) * (abs (2 * (1.5 : ℝ) - 2)) ^ ((1 : ℝ) / 3) +
      2 * (Real.sign (2 * (1.5 : ℝ) - 2)) * (abs (2 * (1.5 : ℝ) - 2)) ^ ((1 : ℝ) / 5) +
      (abs (2 * (1.5 : ℝ) - 2)) ^ ((1 : ℝ) / 7) := by
    specialize hp 1.5
    norm_num [Set.mem_Icc] at hp ⊢
    all_goals linarith
  rw [h1]
  have h2 : (2 * (1.5 : ℝ) - 2) = (1 : ℝ) := by norm_num
  have h3 : Real.sign (2 * (1.5 : ℝ) - 2) = 1 := by
    rw [h2]
    norm_num [Real.sign_of_pos]
  have h4 : abs (2 * (1.5 : ℝ) - 2) = (1 : ℝ) := by
    rw [h2]
    norm_num [abs]
  rw [h3, h4]
  have h5 : (1 : ℝ) ^ ((1 : ℝ) / 3) = 1 := by
    simp
  have h6 : (1 : ℝ) ^ ((1 : ℝ) / 5) = 1 := by
    simp
  have h7 : (1 : ℝ) ^ ((1 : ℝ) / 7) = 1 := by
    simp
  rw [h5, h6, h7]
  all_goals norm_num