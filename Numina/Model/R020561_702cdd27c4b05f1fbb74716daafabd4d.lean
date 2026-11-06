import Mathlib

theorem algebra_311101 {x : ℕ → ℝ} (hx : ∀ n, x n = abs (x (n - 1) - x (n - 2)))
    (hx1 : x 1 = 1) (hx2 : x 2 = a) (ha : 0 ≤ a) :
    IsLeast {T | 0 < T ∧ Function.Periodic x T} 3 ∧
    ∑ i ∈ Finset.range 2002, x (i + 1) = 1335 := by 
  have h0 := hx 0
  simp at h0
  have h1 := hx 1
  simp [h0] at h1 hx1
  all_goals
    norm_num at hx1 h1
    all_goals linarith