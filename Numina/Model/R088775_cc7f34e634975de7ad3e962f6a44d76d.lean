import Mathlib

theorem algebra_158934 (n : ℕ) (h₀ : n = 10) (x : Fin 3 → ℝ)
    (hx : x 0 = 1250 ∧ x 1 = 1270 ∧ x 2 = 1280) (n' : Fin 3 → ℕ)
    (hn' : n' 0 = 2 ∧ n' 1 = 5 ∧ n' 2 = 3) :
    (∑ i : Fin 3, x i * n' i) / n = 1269 := by 
  rcases hx with ⟨hx0, hx1, hx2⟩
  rcases hn' with ⟨hn0, hn1, hn2⟩
  rw [h₀]
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, hx0, hx1, hx2, hn0, hn1, hn2]
  <;> norm_num
  <;> ring_nf <;> norm_num