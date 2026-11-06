import Mathlib

theorem number_theory_112071 (a : ℕ → ℕ) 
    (ha : ∀ n, 0 < n → a n = (Nat.digits 10 (a (n - 1))).sum * 31)
    (ha0 : a 0 = 2020) : 
  a 2019 = 310 := by
  have ha1 : a 1 = 124 := by
    have h1 : a 1 = (Nat.digits 10 (a 0)).sum * 31 := ha 1 (by linarith)
    rw [h1, ha0]
    norm_num
  have ha2 : a 2 = 217 := by
    have h2 : a 2 = (Nat.digits 10 (a 1)).sum * 31 := ha 2 (by linarith)
    rw [h2, ha1]
    norm_num
  have ha3 : a 3 = 310 := by
    have h3 : a 3 = (Nat.digits 10 (a 2)).sum * 31 := ha 3 (by linarith)
    rw [h3, ha2]
    norm_num
  have h1 : ∀ k : ℕ, a (3 * k + 1) = 124 ∧ a (3 * k + 2) = 217 ∧ a (3 * k + 3) = 310 := by 
    intro k
    induction k with 
    | zero =>
      constructor
      · exact ha1 
      constructor 
      · exact ha2 
      · exact ha3 
    | succ k ih =>
      have h4 : a (3 * (k + 1) + 1) = 124 := by
        have eq1 : 3 * (k + 1) + 1 = (3 * k + 3) + 1 := by
          omega 
        rw [eq1]
        have eq2 : a ( (3 * k + 3) + 1 ) = (Nat.digits 10 (a (3 * k + 3)) ).sum * 31 := by 
          apply ha 
          omega 
        rw [eq2] 
        have eq3 : a (3 * k + 3) = 310 := (ih.right.right)
        rw [eq3] 
        all_goals norm_num
      have h5 : a (3 * (k + 1) + 2) = 217 := by
        have eq1 : 3 * (k + 1) + 2 = (3 * (k + 1) + 1) + 1 := by 
          omega 
        rw [eq1] 
        have eq2 : a ( (3 * (k + 1) + 1) + 1 ) = (Nat.digits 10 (a (3 * (k + 1) + 1) ) ).sum * 31 := by 
          apply ha 
          omega 
        rw [eq2] 
        have eq3 : a (3 * (k + 1) + 1 ) = 124 := h4 
        rw [eq3] 
        all_goals norm_num 
      have h6 : a (3 * (k + 1) + 3) = 310 := by
        have eq1 : 3 * (k + 1) + 3 = (3 * (k + 1) + 2) + 1 := by 
          omega 
        rw [eq1] 
        have eq2 : a ( (3 * (k + 1) + 2) + 1 ) = (Nat.digits 10 (a (3 * (k + 1) + 2 ) )).sum * 31 := by 
          apply ha 
          omega 
        rw [eq2] 
        have eq3 : a (3 * (k + 1) + 2 ) = 217 := h5 
        rw [eq3] 
        all_goals norm_num 
      constructor 
      · exact h4 
      constructor 
      · exact h5 
      · exact h6 
  have h2019 : a 2019 = 310 := by 
    have eq3 := (h1 672).right.right
    norm_num at eq3 ⊢ 
    all_goals try exact eq3 
    all_goals try omega 
  exact h2019