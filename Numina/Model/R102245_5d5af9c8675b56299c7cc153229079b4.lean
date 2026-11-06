import Mathlib

open Polynomial

theorem algebra_21854 {p q: ℝ[X]} (hpdegree: p.natDegree = 2) (hqdegree: q.natDegree = 2)
    (h: ∀ x, p.eval x / q.eval x = -(x + 5) * (x - 4) / (x - 2) ^ 2) :
    (p.eval (-1))/(q.eval (-1)) = 20 / 9 := by
        have h1 := h (-1)
        norm_num at h1 ⊢
        all_goals
            linarith