import Mathlib

theorem number_theory_71059 (k : ℤ) (f : ℤ → ℤ) (h : ∀ n, f n * f (n + 1) = (f n + n - k)^2)
    (hk : k > -2) (hf2 : f (-2) = -1) (hf3 : f (-1) = 0) :
    ∀ n, f n = (n - k)^2 := by
  have eq1 := h (-2)
  rw [show f (-2) = -1 by linarith [hf2] ] at eq1
  rw [show f (-2 + 1) = 0 by 
    have : -2 + 1 = -1 := by omega 
    rw [this] 
    simpa using hf3 
  ] at eq1
  have h1 : (-3 - k) ^ 2 = 0 := by
    nlinarith 
  have h2 : -3 - k = 0 := by
    apply pow_eq_zero 
    exact h1 
  have h3 : k = -3 := by 
    linarith 
  nlinarith