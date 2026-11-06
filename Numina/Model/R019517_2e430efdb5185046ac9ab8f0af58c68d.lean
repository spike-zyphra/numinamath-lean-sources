import Mathlib

theorem algebra_200731 (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (d : Fin n → ℝ) (hd : ∀ i, 0 < d i)
    (h : ∀ i, a i = d i) :
    ∑ i, a i * d i = ∑ i, d i * a i := by
  congr
  funext i
  rw [mul_comm]