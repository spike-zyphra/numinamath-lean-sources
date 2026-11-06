import Mathlib


theorem algebra_200481 (k : ℝ) (h : ∃ x y, x ∈ Set.Ioo 0 1 ∧ y ∈ Set.Ioo 1 2 ∧
    7*x^2-(k+13)*x+k^2-k-2=0 ∧ 7*y^2-(k+13)*y+k^2-k-2=0) :
    -2 < k ∧ k < -1 ∨ 3 < k ∧ k < 4 := by

  rcases h with ⟨x, y, hx, hy, h1, h2⟩
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy1, hy2⟩

  have h3 : k ^ 2 - k - 2 > 0 := by
    nlinarith [h1, sq_pos_of_pos (show 0 < x by linarith), sq_pos_of_pos (show 0 < (1 - x) by nlinarith), sq_pos_of_pos (show 0 < (y - 1) by nlinarith), sq_pos_of_pos (show 0 < (2 - y) by nlinarith)]

  have h4 : k ^ 2 - 2 * k - 8 < 0 := by
    nlinarith [h1, sq_pos_of_pos (show 0 < x by linarith), sq_pos_of_pos (show 0 < (1 - x) by nlinarith), sq_pos_of_pos (show 0 < (y - 1) by nlinarith), sq_pos_of_pos (show 0 < (2 - y) by nlinarith)]

  have h5 : k ^ 2 - 3 * k > 0 := by
    nlinarith [h2, sq_pos_of_pos (show 0 < (y - 1) by nlinarith), sq_pos_of_pos (show 0 < (2 - y) by nlinarith), sq_pos_of_pos (show 0 < x by linarith), sq_pos_of_pos (show 0 < (1 - x) by nlinarith)]


  have h6 : k < -1 ∨ k > 2 := by
    by_contra h
    push_neg at h
    nlinarith [sq_nonneg (k - 2), sq_nonneg (k + 1)]


  have h7 : -2 < k ∧ k < 4 := by
    constructor
    · nlinarith
    · nlinarith

  have h8 : k < 0 ∨ k > 3 := by
    by_contra h
    push_neg at h
    nlinarith [sq_nonneg (k - 3), sq_nonneg (k)]

  rcases h6 with (h9 | h10)
  · -- k < -1
    have h9' : -2 < k := by nlinarith
    left
    constructor <;> nlinarith
  · -- k > 2
    rcases h8 with (h11 | h12)
    · -- k < 0
      nlinarith
    · -- k > 3
      right
      constructor <;> nlinarith