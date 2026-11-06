import Mathlib

theorem number_theory_128653 {u : ℕ → ℕ} (hu : ∀ n, u n = u (n - 1) + u (n - 2)) (h : u 0 = 0) (h1 : u 1 = 1) (n : ℕ) (hn : 5 ∣ n) :
    5 ∣ u n := by 
  have h2 := hu 1 
  have h3 := hu 0 
  simp at h2 h3 
  omega