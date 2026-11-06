import Mathlib

theorem algebra_172844 (a : ℕ → ℝ) (h : ∃ r, ∀ n, a n = a 0 * r ^ n)
    (ha : ∀ n, 0 < a n) (h1 : a 2 * a 6 + 2 * a 4 * a 5 + a 1 * a 9 = 25) :
    a 4 + a 5 = 5 := by
  rcases h with ⟨r, hr⟩
  have h2 : a 2 = a 0 * r ^ 2 := by
    specialize hr 2
    simpa using hr
  have h6 : a 6 = a 0 * r ^ 6 := by
    specialize hr 6
    simpa using hr
  have h4 : a 4 = a 0 * r ^ 4 := by
    specialize hr 4
    simpa using hr
  have h5 : a 5 = a 0 * r ^ 5 := by
    specialize hr 5
    simpa using hr
  have h1' : a 1 = a 0 * r ^ 1 := by
    specialize hr 1
    simpa using hr
  have h9 : a 9 = a 0 * r ^ 9 := by
    specialize hr 9
    simpa using hr
  rw [h2, h6, h4, h5, h1', h9] at h1
  have h3 : (a 0 * r ^ 4 * (1 + r)) ^ 2 = 25 := by
    nlinarith
  have h4_pos : 0 < a 4 := by
    apply ha 4
  have h5_pos : 0 < a 5 := by
    apply ha 5
  have h45_pos : 0 < a 4 + a 5 := by
    positivity
  have h_eq : (a 4 + a 5) ^ 2 = 25 := by
    calc
      (a 4 + a 5) ^ 2 = (a 0 * r ^ 4 + a 0 * r ^ 5) ^ 2 := by 
        rw [h4, h5]
      _ = (a 0 * r ^ 4 * (1 + r)) ^ 2 := by 
        ring
      _ = 25 := h3
  have h6 : a 4 + a 5 = 5 := by
    nlinarith [show 0 ≤ a 4 by linarith, show 0 ≤ a 5 by linarith, h_eq]
  exact h6