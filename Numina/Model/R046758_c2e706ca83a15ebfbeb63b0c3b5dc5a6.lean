import Mathlib

theorem number_theory_198437 (a : ℕ → ℕ)
    (h₀ : a 1 = 1)
    (h₁ : ∀ n, Even n → a (2 * n) = a n)
    (h₂ : ∀ n, Odd n → a (2 * n) = 2 * a n)
    (h₃ : ∀ n, Even n → a (2 * n + 1) = 2 * a n + 1)
    (h₄ : ∀ n, Odd n → a (2 * n + 1) = a n) :
    IsLeast {n | 0 < n ∧ a n = a 2017} 5 := by

  have ha1 : a 1 = 1 := h₀
  have ha2 : a 2 = 2 := by
    specialize h₂ 1 (by decide)
    norm_num [ha1] at h₂ ⊢
    linarith
  have ha3 : a 3 = 1 := by
    specialize h₄ 1 (by decide)
    norm_num [ha1] at h₄ ⊢
    linarith
  have ha4 : a 4 = 2 := by
    specialize h₁ 2 (by decide)
    norm_num [ha2] at h₁ ⊢
    linarith
  have ha5 : a 5 = 5 := by
    specialize h₃ 2 (by decide)
    norm_num [ha2] at h₃ ⊢
    linarith

  have ha7 : a 7 = 1 := by
    have h7 : (7 : ℕ) = 2 * 3 + 1 := by norm_num
    rw [h7]
    have h3_odd : Odd (3 : ℕ) := by 
      exact ⟨1, by norm_num⟩
    specialize h₄ 3 (by decide)
    norm_num [ha3, h₄]
  
  have ha15 : a 15 = 1 := by
    have h15 : (15 : ℕ) = 2 * 7 + 1 := by norm_num
    rw [h15]
    have h7_odd : Odd (7 : ℕ) := by 
      exact ⟨3, by norm_num⟩
    specialize h₄ 7 (by decide)
    norm_num [ha7, h₄]

  have ha31 : a 31 = 1 := by
    have h31 : (31 : ℕ) = 2 * 15 + 1 := by norm_num
    rw [h31]
    have h15_odd : Odd (15 : ℕ) := by 
      exact ⟨7, by norm_num⟩
    specialize h₄ 15 (by decide)
    norm_num [ha15, h₄]

  have ha63 : a 63 = 1 := by
    have h63 : (63 : ℕ) = 2 * 31 + 1 := by norm_num
    rw [h63]
    have h31_odd : Odd (31 : ℕ) := by 
      exact ⟨15, by norm_num⟩
    specialize h₄ 31 (by decide)
    norm_num [ha31, h₄]

  have ha126 : a 126 = 2 := by
    specialize h₂ 63 (by decide)
    norm_num [ha63] at h₂ ⊢
    linarith

  have ha252 : a 252 = 2 := by
    specialize h₁ 126 (by decide)
    norm_num [ha126] at h₁ ⊢
    linarith

  have ha504 : a 504 = 2 := by
    specialize h₁ 252 (by decide)
    norm_num [ha252] at h₁ ⊢
    linarith

  have ha1008 : a 1008 = 2 := by
    specialize h₁ 504 (by decide)
    norm_num [ha504] at h₁ ⊢
    linarith

  have ha2017 : a 2017 = 5 := by
    have h2017 : (2017 : ℕ) = 2 * 1008 + 1 := by norm_num
    rw [h2017]
    have h1008_even : Even (1008 : ℕ) := by 
      exact ⟨504, by norm_num⟩
    specialize h₃ 1008 (by decide)
    norm_num [ha1008] at h₃ ⊢
    linarith

  constructor
  · -- Show that 5 is in the set
    constructor
    · -- Show that 5 is positive
      norm_num
    · -- Show that a 5 = a 2017
      have h_eq : a 5 = a 2017 := by
        rw [ha5, ha2017]
      linarith [h_eq, ha5, ha2017]
  · -- Show that 5 is the smallest
    intro n hn
    rcases hn with ⟨hn_pos, h_eq⟩
    by_contra h
    push_neg at h
    have h1 : n < 5 := h
    interval_cases n <;> norm_num [ha1, ha2, ha3, ha4, ha2017] at h_eq