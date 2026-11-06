import Mathlib

theorem algebra_11149 {a : ℝ} (ha : a > 0) (f g : ℝ → ℝ)
    (hf : f = fun x => x ^ 2 + 8) (hg : g = fun x => x ^ 2 - 4) :
    f (g a) = 8 ↔ a = 2 := by
  constructor
  · -- Assume f (g a) = 8, prove a = 2
    intro h
    have h1 : f (g a) = (a ^ 2 - 4) ^ 2 + 8 := by
      rw [hg]
      rw [hf]
      all_goals simp
      <;> ring
    rw [h1] at h
    have h2 : (a ^ 2 - 4) ^ 2 = 0 := by
      nlinarith
    have h3 : a ^ 2 - 4 = 0 := by
      rw [sq_eq_zero_iff] at h2
      exact h2
    have h4 : a ^ 2 = 4 := by 
      linarith
    have h5 : a = 2 := by 
      nlinarith
    exact h5
  · -- Assume a = 2, prove f (g a) = 8
    intro h
    rw [h]
    have h1 : f (g (2 : ℝ)) = 8 := by 
      rw [hg]
      rw [hf]
      norm_num
    exact h1