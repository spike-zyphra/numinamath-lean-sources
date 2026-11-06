import Mathlib

open scoped BigOperators

theorem algebra_126030 {a : ℕ → ℝ}
  (ha1 : a 1 = 1)
  (han : ∀ n ≥ 1, a (n + 1) = a n + 1 / a n) :
  a 100 > 14 := by
  have h1 : ∀ (n : ℕ), a (n + 1) ≥ 1 := by
    intro n 
    induction n with
    | zero => 
        norm_num [ha1]
    | succ n ih =>
      have h2 : a (n + 1) ≥ 1 := ih
      have h3 : a (n + 2) ≥ 1 := by
        have h4 : a (n + 2) = a (n + 1) + 1 / (a (n + 1)) := by
          specialize han (n + 1) (by linarith)
          simpa using han
        rw [h4]
        have h5 : a (n + 1) ≥ 1 := h2
        have h6 : (1 / (a (n + 1)) ) ≥ 0 := by
          apply div_nonneg 
          norm_num 
          linarith 
        have h7 : a (n + 1) + (1 / (a (n + 1)) ) ≥ 1 := by 
          nlinarith [h5, h6] 
        linarith 
      exact h3 
  have h8 : ∀ (n : ℕ), a (n + 1) ^ 2 ≥ 1 + (2 * (n : ℝ)) := by 
    intro n 
    induction n with 
    | zero => 
      rw [ha1]
      norm_num 
    | succ n ih =>
      have h3 : a (n + 2) = a (n + 1) + 1 / (a (n + 1)) := by 
        specialize han (n + 1) (by linarith)
        simpa using han 
      have h6 : a (n + 1) ≥ 1 := h1 n 
      have eq1 : a (n + 2) ^ 2 = a (n + 1) ^ 2 + 2 + 1 / (a (n + 1) ^ 2) := by 
        rw [h3] 
        field_simp 
        <;> ring 
      have h10 : a (n + 1) ^ 2 ≥ 1 + (2 * (n : ℝ)) := by 
        simpa using ih 
      have eq2 : a (n + 2) ^ 2 ≥ 1 + (2 * (n + 1 : ℝ)) := by 
        have eq3 : a (n + 2) ^ 2 = a (n + 1) ^ 2 + 2 + 1 / (a (n + 1) ^ 2) := eq1 
        have h6 : a (n + 1) ≥ 1 := h1 n 
        have h7 : 1 / (a (n + 1) ^ 2) ≥ 0 := by 
          apply div_nonneg
          norm_num 
          nlinarith 
        linarith [eq3, h10, h7] 
      exact_mod_cast eq2 
  by_contra h 
  push_neg at h 
  have h13 : a 100 ≥ 1 := h1 99 
  have h12 : a 100 ^ 2 ≤ 196 := by 
    nlinarith 
  have eq4 : a 100 ^ 2 ≥ 199 := by 
    specialize h8 99 
    norm_num at h8 ⊢ 
    nlinarith 
  nlinarith [show a 100 ≥ 0 by nlinarith [h1 99]]