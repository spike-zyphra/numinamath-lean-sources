import Mathlib

theorem number_theory_243414 (n : ℕ) (h : ∃ k : ℕ, (Nat.digits 10 n).Perm (List.replicate 2018 1 ++ List.replicate 2018 2 ++ List.replicate k 0)) : ¬ IsSquare n := by 
  rcases h with ⟨k, hk⟩ 
  by_contra h1 
  rcases h1 with ⟨r, hr⟩ 
  have h2 : n % 9 = 6 := by 
    have h3 : n % 9 = (Nat.digits 10 n).sum % 9 := by 
      rw [Nat.modEq_nine_digits_sum (n)]
    have h4 : (Nat.digits 10 n).sum = (List.replicate 2018 1 ++ List.replicate 2018 2 ++ List.replicate k 0).sum := by
      have h5 : (Nat.digits 10 n).Perm (List.replicate 2018 1 ++ List.replicate 2018 2 ++ List.replicate k 0) := hk 
      have h6 : (Nat.digits 10 n).sum = (List.replicate 2018 1 ++ List.replicate 2018 2 ++ List.replicate k 0).sum := by
        exact h5.sum_eq 
      linarith 
    rw [h4] at h3 
    have h7 : (List.replicate 2018 1 ++ List.replicate 2018 2 ++ List.replicate k 0).sum % 9 = 6 := by
      have eq1 : (List.replicate 2018 1 ++ List.replicate 2018 2 ++ List.replicate k 0).sum = (List.replicate 2018 1).sum + (List.replicate 2018 2).sum + (List.replicate k 0).sum := by 
        rw [List.sum_append, List.sum_append]
        <;> rfl
      rw [eq1]
      have eq2 : (List.replicate 2018 1).sum = 2018 := by 
        native_decide 
      have eq3 : (List.replicate 2018 2).sum = 4036 := by 
        native_decide 
      have eq4 : (List.replicate k 0).sum = 0 := by 
        simp [List.sum_replicate] 
      rw [eq2, eq3, eq4]
      all_goals try { 
        norm_num 
      }
    omega 
  have h3 : r ^ 2 % 9 = 0 ∨ r ^ 2 % 9 = 1 ∨ r ^ 2 % 9 = 4 ∨ r ^ 2 % 9 = 7 := by 
    have h4 : r ^ 2 % 9 = 0 ∨ r ^ 2 % 9 = 1 ∨ r ^ 2 % 9 = 4 ∨ r ^ 2 % 9 = 7 := by 
      have h5 : r % 9 = 0 ∨ r % 9 = 1 ∨ r % 9 = 2 ∨ r % 9 = 3 ∨ r % 9 = 4 ∨ r % 9 = 5 ∨ r % 9 = 6 ∨ r % 9 = 7 ∨ r % 9 = 8 := by 
        omega 
      rcases h5 with (h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5)
      · -- r ≡ 0 
        simp [Nat.pow_mod, h5]
      · -- r ≡ 1 
        simp [Nat.pow_mod, h5]
      · -- r ≡ 2 
        simp [Nat.pow_mod, h5]
      · -- r ≡ 3 
        simp [Nat.pow_mod, h5]
      · -- r ≡ 4 
        simp [Nat.pow_mod, h5]
      · -- r ≡ 5 
        simp [Nat.pow_mod, h5]
      · -- r ≡ 6 
        simp [Nat.pow_mod, h5]
      · -- r ≡ 7 
        simp [Nat.pow_mod, h5]
      · -- r ≡ 8 
        simp [Nat.pow_mod, h5]
    assumption 
  have h4 : r ^ 2 = n := by 
    linarith [hr]
  have h5 : r ^ 2 % 9 = n % 9 := by 
    omega 
  have h6 : r ^ 2 % 9 = 6 := by 
    omega 
  omega