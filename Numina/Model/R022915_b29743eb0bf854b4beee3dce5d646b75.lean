import Mathlib

theorem algebra_214979 (x : ℕ → ℝ) (h : ∀ n, 2 ≤ n → x n ≠ x (n - 1)) (h' : ∀ n, 2 ≤ n → x n ≠ x (n + 1))
    (h'' : ∀ n, 2 ≤ n → x n = (x (n - 1) + 298 * x n + x (n + 1)) / 300) :
    Real.sqrt ((x 2023 - x 2) / 2021 * (2022 / (x 2023 - x 1))) - 2023 = -2022 := by
  -- Prove that $x_{k+1} - x_k = x_k - x_{k-1}$ for all $k \ge 2$.
  have h2 : ∀ k : ℕ, 2 ≤ k → x (k + 1) - x k = x k - x (k - 1) := by
    intro k hk0
    have h8 := h'' k hk0
    -- Manipulate h'' to get our goal
    have eq1 : 300 * x k = x (k - 1) + 298 * x k + x (k + 1) := by
      have eq2 : x k = (x (k - 1) + 298 * x k + x (k + 1)) / 300 := h8
      linarith
    -- Simplify eq1 to get a recurrence relation
    have eq3 : 2 * x k = x (k - 1) + x (k + 1) := by
      linarith
    -- Rearrange to the claimed equality
    have eq4 : x (k + 1) - x k = x k - x (k - 1) := by
      linarith
    exact eq4
  
  -- Prove that $x_{n+1}-x_n = x_2-x_1$ for all $n \ge 2$.
  have h6 : ∀ k : ℕ, x (k + 2) - x (k + 1) = x 2 - x 1 := by
    intro k
    induction k with 
    | zero =>
      norm_num 
      <;> linarith [ h2 2 (by norm_num) ]
    | succ k ih =>
      have eq6 : x ((k + 1) + 2) - x ((k + 1) + 1) = x 2 - x 1 := by
        have eq11 : x ((k + 1 + 2)) - x (k + 1 + 1) = x (k + 1 + 1) - x (k + 1) := by 
          have h70 : 2 ≤ (k + 1 + 1 : ℕ) := by 
            omega 
          specialize h2 (k + 1 + 1) h70 
          simpa using h2 
        have eq4 : x (k + 1 + 1) - x (k + 1) = x 2 - x 1 := by
          simpa using ih 
        linarith [eq11, eq4]
      simpa using eq6
  
  -- Prove that $x_n = x_2 + (n-2)(x_2-x_1)$ for all $n \ge 2$.
  have h7 : ∀ n : ℕ, 2 ≤ n → x n = x 2 + (n - 2) * (x 2 - x 1) := by
    intro n hn
    have h60 : ∀ k : ℕ, x (k + 2) = x 2 + ↑k * (x 2 - x 1) := by 
      intro k
      induction k with
      | zero => 
        simp 
      | succ k ih =>
        have eq10 : x (k + 1 + 2) = x (k + 2) + (x 2 - x 1) := by
          have eq11 : x ((k + 1 + 2)) - x ((k + 1 + 1)) = x 2 - x 1 := by 
            apply h6 (k + 1) 
          -- Now rewrite to get x_{k+1+2}
          linarith
        have eq11 : x (k + 1 + 2) = x 2 + ↑(k + 1) * (x 2 - x 1) := by 
          rw [eq10, ih]
          field_simp at *
          <;> ring
        exact_mod_cast eq11 
    -- For n ≥ 2, apply the formula
    specialize h60 (n - 2)
    have h90 : (n - 2 : ℕ) + 2 = n := by
      omega 
    rw [h90] at h60
    norm_num at h60 ⊢ 
    exact_mod_cast h60
  
  -- Calculate x_2023.
  have eq10 : x 2023 = x 2 + 2021 * (x 2 - x 1) := by 
    specialize h7 2023 (by norm_num)
    norm_num at h7 ⊢
    linarith
  
  -- Calculate x_2023 - x_2.
  have eq80 : x 2023 - x 2 = 2021 * (x 2 - x 1) := by
    nlinarith [ eq10 ]
  
  -- Calculate x_2023 - x_1.
  have eq90 : x 2023 - x 1 = 2022 * (x 2 - x 1) := by 
    have eq110 : x 2 = x 1 + (x 2 - x 1) := by 
      nlinarith 
    nlinarith [ eq110, eq10 ]
  
  have eq5 : (x 2023 - x 2) / (2021 : ℝ) * (2022 / (x 2023 - x 1)) = 1 := by
    have h4 : x 2 - x 1 ≠ 0 := by
      by_contra h4
      have h0 : x 2 = x 1 := by linarith 
      -- Apply the given distinctness hypothesis
      have h00 : x 2 ≠ x 1 := by 
        apply h 2
        all_goals norm_num 
      contradiction 
    -- Now manipulate the expression
    rw [ show (x 2023 - x 2) / (2021 : ℝ) = x 2 - x 1 by 
      field_simp at *
      all_goals nlinarith [eq80]
      ]
    rw [ show (x 2023 - x 1) = 2022 * (x 2 - x 1) by linarith [eq90] ]
    field_simp [ h4 ]
    <;> nlinarith
  
  have h5 : Real.sqrt ((x 2023 - x 2) / 2021 * (2022 / (x 2023 - x 1))) = 1 := by
    rw [show (x 2023 - x 2) / 2021 * (2022 / (x 2023 - x 1)) = (1 : ℝ) by 
      linarith [ eq5 ]
    ]
    exact Real.sqrt_one

  rw [h5]
  all_goals norm_num