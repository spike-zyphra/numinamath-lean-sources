import Mathlib

theorem inequalities_38225 (a b c : ℝ) (h : ∀ x ∈ Set.Icc (-1) 1, |a * x ^ 2 + b * x + c| ≤ 1)
    (x : ℝ) (hx : x ∈ Set.Icc (-1) 1) :
    |c * x ^ 2 + b * x + a| ≤ 2 := by
  have h1 := h 1 (by norm_num)
  have h2 := h (-1) (by norm_num)
  have h3 := h (0) (by norm_num)
  have h4 := h (1 / 2) (by norm_num)
  have h5 := h (-1 / 2) (by norm_num)
  rcases hx with ⟨hx1, hx2⟩
  have h6 : -1 ≤ x := hx1
  have h7 : x ≤ 1 := hx2
  have h8 : x ^ 2 ≤ 1 := by nlinarith
  have h11 : -1 ≤ a + b + c := by linarith [abs_le.mp h1]
  have h12 : a + b + c ≤ 1 := by linarith [abs_le.mp h1]
  have h21 : -1 ≤ a - b + c := by linarith [abs_le.mp h2]
  have h22 : a - b + c ≤ 1 := by linarith [abs_le.mp h2]
  have h31 : -1 ≤ c := by linarith [abs_le.mp h3]
  have h32 : c ≤ 1 := by linarith [abs_le.mp h3]
  have h13 : -2 ≤ a := by
    nlinarith [abs_le.mp h1, abs_le.mp h2, abs_le.mp h3, abs_le.mp h4, abs_le.mp h5]
  have h14 : a ≤ 2 := by
    nlinarith [abs_le.mp h1, abs_le.mp h2, abs_le.mp h3, abs_le.mp h4, abs_le.mp h5]
  have h18 : -1 ≤ b := by
    nlinarith [abs_le.mp h1, abs_le.mp h2, abs_le.mp h3, abs_le.mp h4, abs_le.mp h5]
  have h19 : b ≤ 1 := by
    nlinarith [abs_le.mp h1, abs_le.mp h2, abs_le.mp h3, abs_le.mp h4, abs_le.mp h5]
  have h17 : -2 ≤ c * x ^ 2 + b * x + a := by
    nlinarith [abs_le.mp h1, abs_le.mp h2, abs_le.mp h3, abs_le.mp h4, abs_le.mp h5, sq_nonneg (x), sq_nonneg (x - 1), sq_nonneg (x + 1)]
  have h18 : c * x ^ 2 + b * x + a ≤ 2 := by
    nlinarith [abs_le.mp h1, abs_le.mp h2, abs_le.mp h3, abs_le.mp h4, abs_le.mp h5, sq_nonneg (x), sq_nonneg (x - 1), sq_nonneg (x + 1)]
  apply abs_le.mpr
  constructor <;> linarith