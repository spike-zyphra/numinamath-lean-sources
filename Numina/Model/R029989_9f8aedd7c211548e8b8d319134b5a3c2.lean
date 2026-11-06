import Mathlib

theorem algebra_160220 {x : ℕ → ℝ} (hx1 : x 1 = 1)
    (hxn : ∀ n ≥ 1, x (n + 1) = Real.sqrt (2 * (x n)^4 + 6 * (x n)^2 + 3)) :
    ∀ n ≥ 1, x n = Real.sqrt ((5^(2^(n - 1)) - 3) / 2) := by 
  intro n hn
  induction n with
  | zero => 
    exfalso 
    linarith 
  | succ n ih =>
    cases n with
    | zero => 
      rw [hx1]
      norm_num 
      <;> ring_nf <;> norm_num
    | succ n => 
      have h1 := ih (by linarith)
      have h2 : x ((n + 1) + 1) = Real.sqrt (2 * (x (n + 1)) ^ 4 + 6 * (x (n + 1)) ^ 2 + 3) := by 
        specialize hxn (n + 1) (by linarith)
        simpa using hxn 
      rw [h2, h1]
      have h3 : Real.sqrt ((5 ^ (2 ^ (n + 1 - 1)) - 3) / 2) ^ 2 = (5 ^ (2 ^ n) - 3) / 2 := by 
        have h4 : Real.sqrt ((5 ^ (2 ^ (n + 1 - 1)) - 3) / 2) ^ 2 = (5 ^ (2 ^ (n + 1 - 1)) - 3) / 2 := by
          apply Real.sq_sqrt
          have h5 : (5 : ℝ) ^ (2 ^ (n + 1 - 1)) ≥ 3 := by 
            have h511 : ∀ m : ℕ, (5 : ℝ) ^ (2 ^ m) ≥ 3 := by
              intro m
              induction m with
              | zero => 
                norm_num 
              | succ m ih => 
                have h7 : (5 : ℝ) ^ (2 ^ (m + 1)) = ((5 : ℝ) ^ (2 ^ m)) ^ 2 := by 
                  ring_nf 
                rw [h7]
                nlinarith [ih]
            have h52 : (n + 1 - 1 : ℕ) = n := by omega 
            rw [h52] at *
            specialize h511 n 
            norm_num at h511 ⊢ 
            all_goals linarith 
          nlinarith 
        have h6 : (5 ^ (2 ^ (n + 1 - 1)) - 3 : ℝ) = (5 ^ (2 ^ n) - 3 : ℝ) := by 
          have h7 : (5 ^ (2 ^ (n + 1 - 1)) : ℝ) = (5 ^ (2 ^ n) : ℝ) := by 
            have h8 : (n + 1 - 1 : ℕ) = n := by omega 
            rw [h8]
            <;> ring_nf 
            all_goals omega 
          linarith [h7]
        rw [h4, h6]
        all_goals norm_num 
        all_goals linarith 
        all_goals norm_num
        all_goals linarith
      have h31 : (Real.sqrt ((5 ^ (2 ^ (n + 1 - 1)) - 3) / 2) : ℝ) ^ 4 = ((5 ^ (2 ^ n) - 3) / 2) ^ 2 := by 
        calc
          (Real.sqrt ((5 ^ (2 ^ (n + 1 - 1)) - 3) / 2) : ℝ) ^ 4 = ( (Real.sqrt ((5 ^ (2 ^ (n + 1 - 1)) - 3) / 2) : ℝ) ^ 2 ) ^ 2 := by ring 
          _ = ((5 ^ (2 ^ n) - 3) / 2) ^ 2 := by 
            rw [h3]
            all_goals norm_num 
          _ = ((5 ^ (2 ^ n) - 3) / 2) ^ 2 := by ring
      have h32 : (2 * (Real.sqrt ((5 ^ (2 ^ (n + 1 - 1)) - 3) / 2) : ℝ) ^ 4 + 6 * (Real.sqrt ((5 ^ (2 ^ (n + 1 - 1)) - 3) / 2) : ℝ) ^ 2 + 3 : ℝ) =
          (5 ^ (2 ^ (n + 1)) - 3) / 2 := by
        rw [h31, h3]
        ring_nf
        <;> norm_num
        <;> ring_nf 
        all_goals 
          have h81 : (5 : ℝ) ^ (2 ^ (n + 1)) = ((5 : ℝ) ^ (2 ^ n)) ^ 2 := by 
            ring_nf
          nlinarith [h81]
        all_goals ring_nf 
        all_goals nlinarith
      have h4 : Real.sqrt (2 * (Real.sqrt ((5 ^ (2 ^ (n + 1 - 1)) - 3) / 2) : ℝ) ^ 4 + 6 * (Real.sqrt ((5 ^ (2 ^ (n + 1 - 1)) - 3) / 2) : ℝ) ^ 2 + 3) =
          Real.sqrt ((5 ^ (2 ^ (n + 1 + 1 - 1)) - 3) / 2) := by
        have h5 : (2 * (Real.sqrt ((5 ^ (2 ^ (n + 1 - 1)) - 3) / 2) : ℝ) ^ 4 + 6 * (Real.sqrt ((5 ^ (2 ^ (n + 1 - 1)) - 3) / 2) : ℝ) ^ 2 + 3 : ℝ) =
            (5 ^ (2 ^ (n + 1 + 1 - 1)) - 3) / 2 := by
          have h61 : (n + 1 + 1 - 1 : ℕ) = n + 1 := by omega 
          rw [h61]
          all_goals 
            try { norm_num }
            try { linarith [h32] }
        rw [h5]
      rw [h4]
      all_goals norm_num 
      <;> ring_nf <;> norm_num 
      all_goals ring_nf <;> norm_num 
      all_goals ring_nf <;> norm_num
      all_goals try { tauto }
      all_goals try { omega }
      all_goals try { linarith [show (5 : ℝ) ^ (2 ^ (n + 1)) ≥ 0 by positivity] }
      all_goals try { nlinarith [Real.sqrt_nonneg ((5 ^ (2 ^ (n + 1 + 1 - 1)) - 3) / 2), Real.sq_sqrt (show ((5 ^ (2 ^ (n + 1 + 1 - 1)) - 3) / 2 : ℝ) ≥ 0 by
        have h511 : ∀ m : ℕ, (5 : ℝ) ^ (2 ^ m) ≥ 3 := by
          intro m
          induction m with
          | zero => 
            norm_num 
          | succ m ih => 
            have h7 : (5 : ℝ) ^ (2 ^ (m + 1)) = ((5 : ℝ) ^ (2 ^ m)) ^ 2 := by 
              ring_nf 
            rw [h7]
            nlinarith [ih]
        have h52 : (n + 1 + 1 - 1 : ℕ) = n + 1 := by omega 
        rw [h52] at *
        specialize h511 (n + 1)
        norm_num at h511 ⊢ 
        all_goals linarith 
      )] }
      all_goals try { nlinarith [Real.sqrt_nonneg (2 * (Real.sqrt ((5 ^ (2 ^ (n + 1 - 1)) - 3) / 2) : ℝ) ^ 4 + 6 * (Real.sqrt ((5 ^ (2 ^ (n + 1 - 1)) - 3) / 2) : ℝ) ^ 2 + 3), Real.sq_sqrt (show (2 * (Real.sqrt ((5 ^ (2 ^ (n + 1 - 1)) - 3) / 2) : ℝ) ^ 4 + 6 * (Real.sqrt ((5 ^ (2 ^ (n + 1 - 1)) - 3) / 2) : ℝ) ^ 2 + 3 : ℝ) ≥ 0 by nlinarith [h32, h3]) ] }