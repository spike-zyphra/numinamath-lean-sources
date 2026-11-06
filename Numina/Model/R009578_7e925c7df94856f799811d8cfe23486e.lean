import Mathlib

theorem algebra_10971 (l w : ℝ) (hlen : 25 * l = 1000 ∨ 25 * w = 1000) (hperi : 10 * 2 * (l + w) = 1000) : l * w = 400 := by
  have h1 : l + w = 50 := by
    linarith
  cases hlen with
  | inl h2 => 
    have h2' : l = 40 := by
      linarith
    have h3 : w = 10 := by
      linarith [h1, h2']
    rw [h2', h3]
    norm_num
  | inr h4 => 
    have h4' : w = 40 := by
      linarith
    have h5 : l = 10 := by
      linarith [h1, h4']
    rw [h5, h4']
    norm_num