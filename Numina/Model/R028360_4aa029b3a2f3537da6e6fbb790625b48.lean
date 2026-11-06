import Mathlib

open Finset

theorem algebra_184247 (a : ℕ → ℤ) (ha1 : a 1 = 2) (ha2 : ∀ n > 0, a n + a (n + 1) = 1) :
    let S n := ∑ i ∈ Icc 1 n, a i
    S 2017 - 2 * S 2018 + S 2019 = 3 := by 
  intro S 
  have h1 : ∀ n > 0, a (n + 1) = 1 - a n := by
    intro n hn
    have h := ha2 n hn
    linarith
  have h2 : ∀ (k : ℕ), a (2 * k + 1) = 2 := by
    intro k 
    induction k with
    | zero =>
      norm_num [ha1]
    | succ k ih =>
      have h4 : a (2 * k + 2) = -1 := by
        have h5 : a (2 * k + 1) + a (2 * k + 2) = 1 := by 
          apply ha2 
          omega 
        rw [ih] at h5 
        linarith 
      have h6 : a (2 * (k + 1) + 1) = 2 := by 
        have h7 : a (2 * k + 2) + a (2 * k + 3) = 1 := by 
          apply ha2 
          omega 
        have h8 : a (2 * k + 3) = 2 := by 
          rw [h4] at h7 
          linarith 
        have h9 : 2 * (k + 1) + 1 = 2 * k + 3 := by 
          omega 
        rw [h9] 
        exact h8 
      exact h6
  have h3 : ∀ (k : ℕ), a (2 * k + 2) = -1 := by
    intro k
    have h11 : a (2 * k + 1) = 2 := h2 k 
    have h5 : a (2 * k + 1) + a (2 * k + 2) = 1 := by 
      apply ha2 
      omega 
    rw [h11] at h5 
    linarith 
  have ha2018 : a 2018 = -1 := by 
    specialize h3 1008 
    norm_num at h3 ⊢ 
    all_goals omega 
  have ha2019 : a 2019 = 2 := by 
    specialize h2 1009 
    norm_num at h2 ⊢ 
    all_goals omega 
  have eq1 : S 2019 = S 2018 + a 2019 := by 
    rw [show S 2019 = ∑ i ∈ Icc 1 2019, a i from rfl]
    rw [show S 2018 = ∑ i ∈ Icc 1 2018, a i from rfl]
    have h8 : ∑ i ∈ Icc 1 2019, a i = (∑ i ∈ Icc 1 2018, a i) + a 2019 := by
      rw [sum_Icc_succ_top (by norm_num)]
    linarith [h8]
  have eq2 : S 2018 = S 2017 + a 2018 := by 
    rw [show S 2018 = ∑ i ∈ Icc 1 2018, a i from rfl]
    rw [show S 2017 = ∑ i ∈ Icc 1 2017, a i from rfl]
    have h9 : ∑ i ∈ Icc 1 2018, a i = (∑ i ∈ Icc 1 2017, a i) + a 2018 := by 
      rw [sum_Icc_succ_top (by norm_num)]
    linarith [h9]
  calc 
    S 2017 - 2 * S 2018 + S 2019 = a 2019 - a 2018 := by 
      linarith [eq1, eq2]
    _ = 3 := by
      rw [ha2019, ha2018]
      all_goals linarith