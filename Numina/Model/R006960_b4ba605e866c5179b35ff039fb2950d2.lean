import Mathlib

theorem number_theory_168484 (a : ℕ → ℤ) (ha : ∀ p k, Nat.Prime p → k > 0 → a (p * k + 1) = p * a k - 3 * a p + 13) :
    a 2013 = 2016 := by
  have h1 := ha 2 1 (by norm_num) (by norm_num)
  have h2 := ha 2 2 (by norm_num) (by norm_num)
  have h3 := ha 5 2 (by norm_num) (by norm_num)
  have h4 := ha 2 5 (by norm_num) (by norm_num)
  have h5 := ha 3 3 (by norm_num) (by norm_num)
  have h6 := ha 3 1 (by norm_num) (by norm_num)
  have h7 := ha 3 2 (by norm_num) (by norm_num)
  have h8 := ha 2 3 (by norm_num) (by norm_num)
  have h9 := ha 3 4 (by norm_num) (by norm_num)
  have h10 := ha 2 6 (by norm_num) (by norm_num)
  have h11 := ha 5 1 (by norm_num) (by norm_num)
  norm_num at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  have ha1 : a 1 = 4 := by
    linarith [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  have ha2 : a 2 = 5 := by
    linarith [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  have h2013 : a 2013 = 2 * a 1006 - 3 * a 2 + 13 := by
    specialize ha 2 1006 (by norm_num) (by norm_num)
    norm_num at ha ⊢
    linarith
  have h1006 : a 1006 = 3 * a 335 - 3 * a 3 + 13 := by
    specialize ha 3 335 (by norm_num) (by norm_num)
    norm_num at ha ⊢
    linarith
  have h335 : a 335 = 2 * a 167 - 3 * a 2 + 13 := by
    specialize ha 2 167 (by norm_num) (by norm_num)
    norm_num at ha ⊢
    linarith
  have h167 : a 167 = 2 * a 83 - 3 * a 2 + 13 := by
    specialize ha 2 83 (by norm_num) (by norm_num)
    norm_num at ha ⊢
    linarith
  have h83 : a 83 = 2 * a 41 - 3 * a 2 + 13 := by
    specialize ha 2 41 (by norm_num) (by norm_num)
    norm_num at ha ⊢
    linarith
  have h41 : a 41 = 2 * a 20 - 3 * a 2 + 13 := by
    specialize ha 2 20 (by norm_num) (by norm_num)
    norm_num at ha ⊢
    linarith
  have h20 : a 20 = 19 * a 1 - 3 * a 19 + 13 := by
    specialize ha 19 1 (by norm_num) (by norm_num)
    norm_num at ha ⊢
    linarith
  have h19 : a 19 = 2 * a 9 - 3 * a 2 + 13 := by
    specialize ha 2 9 (by norm_num) (by norm_num)
    norm_num at ha ⊢
    linarith
  have h9 : a 9 = 2 * a 4 - 3 * a 2 + 13 := by
    specialize ha 2 4 (by norm_num) (by norm_num)
    norm_num at ha ⊢
    linarith
  have h4' : a 4 = 3 * a 1 - 3 * a 3 + 13 := by
    specialize ha 3 1 (by norm_num) (by norm_num)
    norm_num at ha ⊢
    linarith
  have ha3 : a 3 = 6 := by
    linarith [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  rw [h2013, h1006, h335, h167, h83, h41, h20, h19, h9, h4', ha1, ha2, ha3] 
  all_goals omega