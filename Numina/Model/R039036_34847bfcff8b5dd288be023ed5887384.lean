import Mathlib

theorem algebra_219268 (x : ℕ → ℝ) (hx1 : 0 < x 1 ∧ x 1 < 1)
    (hxn : ∀ n, x (n + 1) = x n - (x n)^2) :
    ∀ n, ∑ i ∈ Finset.Icc 1 n, (x i)^2 < 1 := by

  have h2 : ∀ (n : ℕ), 0 < x (n + 1) ∧ x (n + 1) < 1 := by
    intro n
    induction n with
    | zero =>
      exact hx1
    | succ n ih =>
      have eq5 : x ((n + 1) + 1) = x (n + 1) - (x (n + 1)) ^ 2 := by
        specialize hxn (n + 1)
        simpa using hxn
      rw [eq5]
      rcases ih with ⟨h1, h2⟩
      constructor
      · -- Show positive
        nlinarith [sq_pos_of_pos (show (0 : ℝ) < x (n + 1) by linarith), sq_pos_of_pos (show (0 : ℝ) < 1 - x (n + 1) by nlinarith)]
      · -- Show less than 1
        nlinarith [sq_pos_of_pos (show (0 : ℝ) < x (n + 1) by linarith), sq_pos_of_pos (show (0 : ℝ) < 1 - x (n + 1) by nlinarith)]

  have h3 : ∀ (i : ℕ), (x (i + 1)) ^ 2 = x (i + 1) - x (i + 2) := by
    intro i
    have eq1 : x (i + 2) = x (i + 1) - (x (i + 1)) ^ 2 := by
      specialize hxn (i + 1)
      simpa using hxn
    linarith

  intro n

  have h4 : ∀ (n : ℕ), ∑ i ∈ Finset.Icc 1 n, (x i) ^ 2 = x 1 - x (n + 1) := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      have eq5 : ∑ i ∈ Finset.Icc 1 (n + 1), (x i) ^ 2 = ∑ i ∈ Finset.Icc 1 n, (x i) ^ 2 + (x (n + 1)) ^ 2 := by 
        rw [Finset.sum_Icc_succ_top (by norm_num)]
      rw [eq5]
      rw [ih]
      have eq6 : (x (n + 1)) ^ 2 = x (n + 1) - x (n + 2) := by 
        apply h3
      rw [eq6]
      all_goals
        ring

  have h4_rw : ∑ i ∈ Finset.Icc 1 n, (x i) ^ 2 = x 1 - x (n + 1) := h4 n

  have h5 : x (n + 1) > 0 := by 
    have h3_1 : ∀ (n : ℕ), x (n + 1) > 0 := by 
      intro n 
      exact (h2 n).1
    specialize h3_1 n
    linarith

  have h6 : x (n + 1) < 1 := by 
    have h3_1 : ∀ (n : ℕ), x (n + 1) < 1 := by
      intro n
      exact (h2 n).2
    specialize h3_1 n 
    linarith

  rw [h4_rw]
  have hx1_pos : 0 < x 1 := by
    linarith [hx1.1]
  have hx1_lt_one : x 1 < 1 := by
    linarith [hx1.2]

  nlinarith