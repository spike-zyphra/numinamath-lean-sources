import Mathlib

theorem algebra_322766 {a b : ℕ → ℤ} (ha : a 1 = 2007) (ha' : ∀ n ≥ 2, a n > 0)
    (h : ∀ n, a (n + 1) = 2 * b n - a n ∧ b (n + 1) = 2 * a n - b n) :
    b 1 = 2007 := by 
  have h1 := h 0
  have h2 := h 1
  have h3 := h 2
  have h4 := h 3
  have h5 := h 4
  have h6 := h 5
  have h7 := h 6
  have h8 := h 7
  have h9 := h 8
  have h10 := h 9
  norm_num [ha] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 
  have h11 := ha' 2 (by linarith)
  have h12 := ha' 3 (by linarith)
  have h13 := ha' 4 (by linarith)
  have h14 := ha' 5 (by linarith)
  have h15 := ha' 6 (by linarith)
  have h16 := ha' 7 (by linarith)
  have h17 := ha' 8 (by linarith)
  have h18 := ha' 9 (by linarith)
  have h19 := ha' 10 (by linarith)
  norm_num at h11 h12 h13 h14 h15 h16 h17 h18 h19 
  all_goals 
    nlinarith [sq_nonneg (a 0 - 2007 : ℤ), sq_nonneg (b 0 - 2007 : ℤ),
      sq_nonneg (a 1 - 2007 : ℤ), sq_nonneg (b 1 - 2007 : ℤ)]