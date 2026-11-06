import Mathlib

theorem number_theory_2768 (p : ℕ) [hp : Fact (Nat.Prime p)] (f : ℕ → ℕ)
    (h : ∀ n, f n = f (n - 1) + f (n - 2)) (h0 : f 0 = 0) (h1 : f 1 = 1) (h2 : p ∣ f p) :
    p = 5 := by
  have h3 := h 0
  have h4 := h 1
  simp [h0] at h3 h4
  all_goals linarith [h1, h4]