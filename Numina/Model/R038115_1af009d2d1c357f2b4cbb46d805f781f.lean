import Mathlib

theorem number_theory_225196 {P : Polynomial ℤ} (hP : ∃ n, 3 ∣ P.eval n ∧ 3 ∣ P.eval (n + 1) ∧ 3 ∣ P.eval (n + 2)) :
    ∀ m, 3 ∣ P.eval m := by
  rcases hP with ⟨n, hn, hn1, hn2⟩
  intro m
  have h1 : (m - n) % 3 = 0 ∨ (m - n) % 3 = 1 ∨ (m - n) % 3 = 2 := by
    omega
  rcases h1 with h1 | h1 | h1
  · -- Case where m ≡ n (mod 3)
    have h2 : (m - n) % 3 = 0 := h1
    have h3 : 3 ∣ (m - n) := by 
      omega
    have h4 : 3 ∣ (P.eval m - P.eval n) := by
      have h5 : (m - n) ∣ (P.eval m - P.eval n) := by
        apply P.sub_dvd_eval_sub
      have h6 : 3 ∣ (m - n) := by 
        omega
      have h7 : 3 ∣ (P.eval m - P.eval n) := by 
        exact dvd_trans h6 h5
      exact h7
    have h7 : 3 ∣ P.eval m := by
      omega
    exact h7
  · -- Case where m ≡ n+1 (mod 3)
    have h2 : (m - n) % 3 = 1 := h1
    have h4 : (m - (n + 1)) % 3 = 0 := by 
      omega
    have h5 : 3 ∣ (m - (n + 1)) := by 
      omega
    have h6 : 3 ∣ (P.eval m - P.eval (n + 1)) := by 
      have h5' : (m - (n + 1)) ∣ (P.eval m - P.eval (n + 1)) := by
        apply P.sub_dvd_eval_sub
      have h7 : 3 ∣ (m - (n + 1)) := by 
        omega
      have h8 : 3 ∣ (P.eval m - P.eval (n + 1)) := by
        exact dvd_trans h7 h5'
      exact h8
    have h7 : 3 ∣ P.eval m := by
      omega
    exact h7
  · -- Case where m ≡ n + 2 (mod 3)
    have h2 : (m - n) % 3 = 2 := h1
    have h4 : (m - (n + 2)) % 3 = 0 := by
      omega
    have h5 : 3 ∣ (m - (n + 2)) := by 
      omega
    have h6 : 3 ∣ (P.eval m - P.eval (n + 2)) := by 
      have h5' : (m - (n + 2)) ∣ (P.eval m - P.eval (n + 2)) := by 
        apply P.sub_dvd_eval_sub
      have h7 : 3 ∣ (m - (n + 2)) := by 
        omega
      have h8 : 3 ∣ (P.eval m - P.eval (n + 2)) := by 
        exact dvd_trans h7 h5'
      exact h8
    have h7 : 3 ∣ P.eval m := by
      omega
    exact h7