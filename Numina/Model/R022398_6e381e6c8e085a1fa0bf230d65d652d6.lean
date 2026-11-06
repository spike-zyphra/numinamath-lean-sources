import Mathlib

theorem number_theory_7084 (f : ℕ → ℕ) (h1 : f 1 = 1)
    (h2 : ∀ n, f n ≤ f (n + 1)) (h3 : ∀ a, f (2 * a) = f a + 1) :
    f 2016 + f 2017 + f 2018 = 36 := by 
  have h4 := h3 0
  all_goals 
    simp at h4 
    all_goals 
      omega