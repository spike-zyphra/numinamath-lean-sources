import Mathlib

open Real 
open Complex 

theorem algebra_97738 (f : ℂ → ℂ) (hf : ∀ w, f w = w ^ 2 - 19 * w)
    (z : ℂ) (hz : z ≠ 0) (h : ((f (f z) - f z) * (starRingEnd ℂ) (f z - z)).re = 0)
    (m n : ℕ) (hnpos : n > 0) (hmpos : m > 0) (hn_ne_sq : ∀ k, (n : ℝ) ≠ k ^ 2) (h' : m > 0 ∧ n > 0 ∧ z = m + sqrt n + 11 * .I) :
    m + n = 230 := by
  rcases h' with ⟨hm1, hn1, hz_eq⟩
  have h3 : (n : ℝ) = (sqrt (n : ℝ)) ^ 2 := by
    rw [Real.sq_sqrt]
    have hn' : (n : ℝ) ≥ 0 := by positivity
    linarith
  have h5 := hn_ne_sq (sqrt (n : ℝ))
  rw [h3] at h5
  all_goals
    tauto