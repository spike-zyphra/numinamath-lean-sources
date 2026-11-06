import Mathlib

/- An iguana writes the number 1 on the blackboard.
 Every minute afterwards, if the number $x$ is written, the iguana erases it and either writes $\frac{1}{x}$ or $x+1$.
  Can the iguana eventually write the number $\frac{20}{17}$ ? -/

noncomputable def x (n : ℕ) : ℝ :=
  if n = 0 then 1       -- construct the sequence x
  else if n = 1 then 2
  else if n = 2 then 1 / 2
  else if n = 3 then 3 / 2
  else if n = 4 then 2 / 3
  else if n = 5 then 5 / 3
  else if n = 6 then 8 / 3
  else if n = 7 then 11 / 3
  else if n = 8 then 14 / 3
  else if n = 9 then 17 / 3
  else if n = 10 then 3 / 17
  else if n = 11 then 20 / 17
  else x (n - 1) + 1

theorem number_theory_259729: ∃ a: ℕ → ℝ, (∀ n, a (n + 1) = 1 / a n ∨ a (n + 1) = a n + 1) ∧
  a 0 = 1 ∧ ∃ m, a m = 20 / 17 := by

    use x   -- then we verify that x is a solution
    constructor
    .
      intro n
      by_cases ln: n ≤ 10
      
      -- for the case when n ≤ 10
      .
        interval_cases n
        .
          right
          simp [x]
          norm_num
        .
          left
          simp [x]
        .
          right
          simp [x]
          norm_num
        .
          left
          simp [x]
        .
          right
          simp [x]
          norm_num
        .
          right
          simp [x]
          norm_num
        .
          right
          simp [x]
          norm_num
        .
          right
          simp [x]
          norm_num
        .
          right
          simp [x]
          norm_num
        .
          left
          simp [x]
        .
          right
          simp [x]
          norm_num

      -- for the case when n > 10
      .
        simp at ln
        right
        set m:= n + 1 with hm
        rw [show n = m - 1 by omega]
        replace ln: 12 ≤ m := by omega
        rw [x]
        have h0: m ≠ 0 := by
          omega
        have h1: m ≠ 1 := by
          omega
        have h2: m ≠ 2 := by
          omega
        have h3: m ≠ 3 := by
          omega
        have h4: m ≠ 4 := by
          omega
        have h5: m ≠ 5 := by
          omega
        have h6: m ≠ 6 := by
          omega
        have h7: m ≠ 7 := by
          omega
        have h8: m ≠ 8 := by
          omega
        have h9: m ≠ 9 := by
          omega
        have h10: m ≠ 10 := by
          omega
        have h11: m ≠ 11 := by
          omega
        simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

    .
      constructor
      .
        simp [x]
      .
        use 11
        simp [x]