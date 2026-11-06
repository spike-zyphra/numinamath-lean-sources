import Mathlib

open Finset Real

theorem algebra_97150 {T P : ℕ → ℝ} (hT : ∀ n, T n = ∑ i ∈ Icc 1 n, i)
    (hP : P 2 = T 2 / (T 2 - 1) ∧ ∀ n ≥ 3, P n = P (n - 1) * T n / (T n - 1)) :
    P 1991 = 3 * 1991 / 1993 := by

  have h1 : ∀ n, T n = (n : ℝ) * (n + 1) / 2 := by
    intro n
    rw [hT n]
    have h2 : ∀ (m : ℕ), ∑ i in Icc 1 m, (i : ℝ) = (m : ℝ) * (m + 1) / 2 := by 
      intro m 
      induction m with
      | zero =>
        simp 
      | succ m ih =>
        rw [sum_Icc_succ_top (by linarith)]
        rw [ih]
        field_simp at *
        ring
    specialize h2 n 
    simpa using h2
  
  rcases hP with ⟨hP2, hPn⟩

  have eq1 : ∀ n : ℕ, n ≥ 2 → P (n) = 3 * (↑n : ℝ) / (↑n + 2 : ℝ) := by
    intro n hn2
    have eq2 : ∀ n : ℕ, P (n + 2) = 3 * (↑(n + 2) : ℝ) / (↑(n + 2) + 2 : ℝ) := by
      intro n
      induction n with
      | zero =>
        have eq2 : P 2 = T 2 / (T 2 - 1) := by 
          simpa using hP2 
        have eq3 : T 2 = (2 : ℝ) * (2 + 1) / 2 := by 
          specialize h1 2 
          simpa using h1 
        rw [eq2, eq3] 
        norm_num
      | succ n ih =>
        have h5 : P (n + 3) = P (n + 2) * T (n + 3) / (T (n + 3) - 1) := by 
          specialize hPn (n + 3) (by linarith)
          simpa using hPn
        have h4 : P (n + 2) = 3 * (↑(n + 2) : ℝ) / (↑(n + 2) + 2 : ℝ) := by 
          simpa using ih 
        have eq5 : T (n + 3) = (↑(n + 3) : ℝ) * (↑(n + 3) + 1) / 2 := by 
          specialize h1 (n + 3) 
          simpa using h1 
        have eq6 : P (n + 3) = P (n + 2) * T (n + 3) / (T (n + 3) - 1) := h5 
        rw [eq6] 
        rw [h4]
        rw [eq5] 
        field_simp 
        <;> ring_nf <;> field_simp <;> ring
    specialize eq2 (n - 2) 
    have eq3 : n - 2 + 2 = n := by 
      omega 
    rw [eq3] at eq2 
    simpa using eq2
  have eq2 := eq1 1991 (by norm_num)
  norm_num at eq2 ⊢ 
  <;> linarith 
  all_goals try { norm_num } <;> try { linarith }
  all_goals try { linarith }
  all_goals try { tauto } <;> try { nlinarith }
  all_goals try { tauto } <;> try { nlinarith }
  all_goals try { tauto } <;> try { nlinarith } <;> try { tauto }