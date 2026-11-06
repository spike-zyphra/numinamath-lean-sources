import Mathlib

theorem algebra_310109 :
    ∃ (k : ℕ → ℝ) (a b : ℕ → ℝ),
      (∀ n, 1 ≤ n → (1, 1) ∈ {(x, y) | y = k n * x + a n}) ∧
      (∀ n, 1 ≤ n → k (n + 1) = a n - b n) ∧
      (∀ n, 1 ≤ n → k n * k (n + 1) ≥ 0) := by

  use λ n => if n = 0 then (1 : ℝ) else 0
  use λ n => if n = 0 then (0 : ℝ) else 1
  use λ n => if n = 0 then (0 : ℝ) else 1

  constructor
  · -- Show that (1, 1) is on all lines l_n for n ≥ 1
    intro n hn
    have h1 : n ≥ 1 := by omega
    have eq1 : (if n = 0 then (1 : ℝ) else (0 : ℝ)) = (0 : ℝ) := by
      have hn1 : n ≠ 0 := by
        omega
      simp [hn1]
    have eq2 : (if n = 0 then (0 : ℝ) else (1 : ℝ)) = (1 : ℝ) := by
      have hn1 : n ≠ 0 := by
        omega
      simp [hn1]
    simp only [Set.mem_setOf_eq] at *
    rw [eq1, eq2]
    all_goals 
      norm_num
  constructor
  · -- Show condition 2: k_{n+1} = a_n - b_n for all n ≥ 1
    intro n hn
    have h1 : n ≥ 1 := by omega 
    have hk1 : (if n + 1 = 0 then (1 : ℝ) else (0 : ℝ)) = (0 : ℝ) := by
      have hn11 : n + 1 ≠ 0 := by
        omega
      simp [hn11]
    have ha1 : (if n = 0 then (0 : ℝ) else (1 : ℝ)) = (1 : ℝ) := by
      have hn1 : n ≠ 0 := by 
        omega
      simp [hn1]
    simp only [Set.mem_setOf_eq] at *
    simp [hk1, ha1]
    all_goals 
      linarith
  · -- Show the condition 3: k_n * k_{n+1} ≥ 0 for all n ≥ 1
    intro n hn
    have h1 : n ≥ 1 := by omega 
    have eq1 : (if n = 0 then (1 : ℝ) else (0 : ℝ)) = (0 : ℝ) := by
      have hn11 : n ≠ 0 := by
        omega
      simp [hn11]
    have eq2 : (if (n + 1) = 0 then (1 : ℝ) else (0 : ℝ)) = (0 : ℝ) := by
      have hn11 : n + 1 ≠ 0 := by
        omega
      simp [hn11]
    simp only [Set.mem_setOf_eq] at *
    rw [eq1, eq2] 
    all_goals
      norm_num