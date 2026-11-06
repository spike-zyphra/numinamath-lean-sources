import Mathlib

theorem number_theory_319515 (a : ℕ → ℕ) (ha0 : a 0 = 0) (ha1 : a 1 = 1)
    (han : ∀ n, a (2 * n) = a n ∧ a (2 * n + 1) = a n + 1) :
    a 2013 = 9 := by

  have h1 : a 0 = 0 := ha0
  have h2 : a 1 = 1 := ha1

  have h3 : a 3 = a 1 + 1 := by
    specialize han 1
    have h := han.right
    norm_num at h ⊢
    linarith

  have h3' : a 3 = 2 := by
    linarith [h3, h2]

  have h7 : a 7 = a 3 + 1 := by
    specialize han 3
    have h := han.right
    norm_num at h ⊢
    linarith

  have h7' : a 7 = 3 := by
    linarith [h7, h3']

  have h15 : a 15 = a 7 + 1 := by
    specialize han 7
    have h := han.right
    norm_num at h ⊢
    linarith

  have h15' : a 15 = 4 := by
    linarith [h15, h7']

  have h31 : a 31 = a 15 + 1 := by
    specialize han 15
    have h := han.right
    norm_num at h ⊢
    linarith

  have h31' : a 31 = 5 := by
    linarith [h31, h15']

  have h62 : a 62 = a 31 := by
    specialize han 31
    have h := han.left
    norm_num at h ⊢
    linarith

  have h62' : a 62 = 5 := by
    linarith [h62, h31']

  have h125 : a 125 = a 62 + 1 := by
    specialize han 62
    have h := han.right
    norm_num at h ⊢
    linarith

  have h125' : a 125 = 6 := by
    linarith [h125, h62']

  have h251 : a 251 = a 125 + 1 := by
    specialize han 125
    have h := han.right
    norm_num at h ⊢
    linarith

  have h251' : a 251 = 7 := by
    linarith [h251, h125']

  have h503 : a 503 = a 251 + 1 := by
    specialize han 251
    have h := han.right
    norm_num at h ⊢
    linarith

  have h503' : a 503 = 8 := by
    linarith [h503, h251']

  have h1006 : a 1006 = a 503 := by
    specialize han 503
    have h := han.left
    norm_num at h ⊢
    linarith

  have h1006' : a 1006 = 8 := by
    linarith [h1006, h503']

  have h2013 : a 2013 = a 1006 + 1 := by
    specialize han 1006
    have h := han.right
    norm_num at h ⊢
    linarith

  linarith [h2013, h1006']