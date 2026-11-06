import Mathlib

theorem algebra_211543 {x y : ℝ} (hx : x = 1) (hy : y = 2)
    (h : ∃ n, (x + y) / 2 ^ n = 941664 / 665857) :
    (x + y) / 2 ^ (n + 1) ≠ 35 / 24 := by
  rcases h with ⟨n, hn⟩
  have h1 : x + y = 3 := by
    rw [hx, hy]
    norm_num
  rw [h1] at hn
  have h2 : (3 : ℝ) / (2 : ℝ) ^ n = (941664 : ℝ) / 665857 := by
    linarith
  have h3 : (3 : ℝ) * (665857 : ℝ) = (941664 : ℝ) * (2 : ℝ) ^ n := by
    field_simp at h2 ⊢
    nlinarith
  norm_cast at h3 ⊢
  have h4 : (3 : ℤ) * 665857 % 2 = 1 := by
    norm_num
  have h5 : ((941664 : ℤ) * (2 : ℤ) ^ n) % 2 = 0 := by
    omega
  omega