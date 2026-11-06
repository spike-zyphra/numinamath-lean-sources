import Mathlib

open Real

theorem inequalities_275346 (a b c d : ℝ) :
    (a^2 + b^2) * (c^2 + d^2) ≥ (a * c + b * d)^2  ∧ (a * d = b * c → (a^2 + b^2) * (c^2 + d^2) = (a * c + b * d)^2):= by 
  constructor 
  · -- Prove (a^2 + b^2) * (c^2 + d^2) ≥ (a * c + b * d)^2
    have h1 : (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) - (a * c + b * d) ^ 2 = (a * d - b * c) ^ 2 := by
      ring
    have h2 : (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) ≥ (a * c + b * d) ^ 2 := by
      linarith [sq_nonneg (a * d - b * c)]
    linarith
  · -- Prove the equality condition 
    intro h
    have h4 : a * d = b * c := h
    have h5 : (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c + b * d) ^ 2 := by 
      have h4' : a * d = b * c := h
      nlinarith [sq_nonneg (a * d - b * c), sq_nonneg (a * c - b * d), h4']
    linarith [h5]