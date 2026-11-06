import Mathlib
open Real Set

theorem algebra_9000 {f : ℝ → ℝ} (hf : f = λ x => abs (x^2 - 2 * x - 3)) :
    MonotoneOn f (Icc (-1) 1) ∧ MonotoneOn f (Ici 3) ∧ AntitoneOn f (Iic (-1)) ∧ AntitoneOn f (Icc 1 3) := by 
  constructor 
  · -- f is monotonically increasing on Icc (-1) 1
    rw [hf]
    intro x hx y hy hxy 
    simp at hx hy ⊢ 
    rcases hx with ⟨hx1, hx2⟩
    rcases hy with ⟨hy1, hy2⟩ 
    have h1 : (x) ^ 2 - 2 * (x) - 3 ≤ 0 := by 
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1)]
    have h2 : (y) ^ 2 - 2 * (y) - 3 ≤ 0 := by 
      nlinarith [sq_nonneg (y - 1), sq_nonneg (y + 1)]
    have eq1 : abs ((x) ^ 2 - 2 * (x) - 3) = - ((x) ^ 2 - 2 * (x) - 3) := by 
      rw [abs_of_nonpos h1]
    have eq2 : abs ((y) ^ 2 - 2 * (y) - 3) = - ((y) ^ 2 - 2 * (y) - 3) := by 
      rw [abs_of_nonpos h2]
    rw [eq1, eq2]
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1)]
  constructor 
  · -- f is monotonically increasing on Ici 3
    rw [hf]
    intro x hx y hy hxy 
    simp at hx hy ⊢ 
    have h1 : (x) ^ 2 - 2 * (x) - 3 ≥ 0 := by 
      nlinarith [sq_nonneg (x - 3), sq_nonneg (x - 1)]
    have h2 : (y) ^ 2 - 2 * (y) - 3 ≥ 0 := by 
      nlinarith [sq_nonneg (y - 3), sq_nonneg (y - 1)]
    have eq1 : abs ((x) ^ 2 - 2 * (x) - 3) = (x) ^ 2 - 2 * (x) - 3 := by 
      rw [abs_of_nonneg h1]
    have eq2 : abs ((y) ^ 2 - 2 * (y) - 3) = (y) ^ 2 - 2 * (y) - 3 := by 
      rw [abs_of_nonneg h2]
    rw [eq1, eq2]
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - 3), sq_nonneg (y - 3)]
  constructor 
  · -- f is antitone on Iic (-1)
    rw [hf]
    intro x hx y hy hxy 
    simp at hx hy ⊢ 
    have h1 : (x) ^ 2 - 2 * (x) - 3 ≥ 0 := by 
      nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 3)]
    have h2 : (y) ^ 2 - 2 * (y) - 3 ≥ 0 := by 
      nlinarith [sq_nonneg (y + 1), sq_nonneg (y - 3)]
    have eq1 : abs ((x) ^ 2 - 2 * (x) - 3) = (x) ^ 2 - 2 * (x) - 3 := by 
      rw [abs_of_nonneg h1]
    have eq2 : abs ((y) ^ 2 - 2 * (y) - 3) = (y) ^ 2 - 2 * (y) - 3 := by 
      rw [abs_of_nonneg h2]
    rw [eq1, eq2]
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + 1), sq_nonneg (y + 1)]
  · -- f is antitone on Icc 1 3
    rw [hf]
    intro x hx y hy hxy 
    simp at hx hy ⊢ 
    rcases hx with ⟨hx1, hx2⟩
    rcases hy with ⟨hy1, hy2⟩ 
    have h1 : (x) ^ 2 - 2 * (x) - 3 ≤ 0 := by 
      nlinarith [sq_nonneg (x - 3), sq_nonneg (x + 1)]
    have h2 : (y) ^ 2 - 2 * (y) - 3 ≤ 0 := by 
      nlinarith [sq_nonneg (y - 3), sq_nonneg (y + 1)]
    have eq1 : abs ((x) ^ 2 - 2 * (x) - 3) = - ((x) ^ 2 - 2 * (x) - 3) := by 
      rw [abs_of_nonpos h1]
    have eq2 : abs ((y) ^ 2 - 2 * (y) - 3) = - ((y) ^ 2 - 2 * (y) - 3) := by 
      rw [abs_of_nonpos h2]
    rw [eq1, eq2]
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - 3), sq_nonneg (y - 1), sq_nonneg (y - 3), sq_nonneg (x - 1)]