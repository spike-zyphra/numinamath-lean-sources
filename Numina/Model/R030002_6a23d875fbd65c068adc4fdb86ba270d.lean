import Mathlib

def u : ℕ → ℝ
| 0 => 17 * (1 + 2)
| 1 => 17 ^ 2 * (2 + 2)
| n + 2 => 17 ^ (n + 2) * (n + 3)

theorem algebra_103107 {a b : ℝ} (h : ∀ n, u (n + 2) = a * u (n + 1) + b * u n) :
    a ^ 2 - b = 1445 := by
  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h 2
  simp [u] at eq1 eq2 eq3
  ring_nf at eq1 eq2 eq3 
  have h1 : a = 34 := by
    nlinarith 
  have h2 : b = -289 := by
    nlinarith 
  rw [h1, h2]
  norm_num