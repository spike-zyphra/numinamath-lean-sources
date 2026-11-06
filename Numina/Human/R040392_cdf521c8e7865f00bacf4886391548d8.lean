import Mathlib

theorem algebra_173356 {a : ℕ → ℝ} (h : ∃ d, ∀ n, a n = a 0 + d * n)
(h' : ∀ n, a n + 2 * a (n + 1) + 3 * a (n + 2) = 6 * n + 22) :
a 2017 = 6058 / 3 := by
  rcases h with ⟨d, hd⟩
  have eq1 := h' 0
  have eq2 := h' 1
  have eq3 := h' 2
  simp [hd 1, hd 2, hd 3] at eq1 eq2 eq3
  ring_nf at eq1 eq2 eq3
  have h1 : d = 1 := by
    linarith
  have h2 : a 0 = 7 / 3 := by
    linarith [h1, eq1]
  have a2017 : a 2017 = a 0 + d * 2017 := by
    rw [hd 2017]
    ring
  rw [h2, h1] at a2017
  norm_num at a2017
  linarith