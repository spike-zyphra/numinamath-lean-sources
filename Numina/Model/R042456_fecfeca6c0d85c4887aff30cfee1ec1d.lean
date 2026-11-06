import Mathlib

theorem algebra_173412 {a : ℕ → ℝ} (ha0 : a 0 = 1) 
    (hrec : ∀ n, a (n+1) = (9/11) * a n + 1/11) :
    Filter.Tendsto a Filter.atTop (nhds (1/2)) := by
  have h1 : ∀ n, a n = 1 / 2 + (1 / 2) * ((9 / 11) ^ n) := by 
    intro n 
    induction n with 
    | zero => 
      rw [ha0]
      norm_num
    | succ n ih => 
      rw [hrec n, ih]
      field_simp
      ring_nf 
  have eq2 : ∀ n, a n = 1 / 2 + (1 / 2) * ((9 / 11) ^ n) := h1 
  have h2 : Filter.Tendsto a Filter.atTop (nhds (1/2)) := by
    have eq3 : a = fun n : ℕ => 1 / 2 + (1 / 2) * ((9 / 11) ^ n) := by 
      funext n 
      exact_mod_cast eq2 n 
    rw [eq3]
    have h3 : Filter.Tendsto (fun (n : ℕ) => ((9 / 11 : ℝ) ^ n)) Filter.atTop (nhds (0 : ℝ)) := by 
      apply tendsto_pow_atTop_nhds_zero_of_lt_one
      all_goals 
        norm_num 
    have h4 : Filter.Tendsto (fun (n : ℕ) => (1 / 2 : ℝ) + (1 / 2 : ℝ) * ((9 / 11 : ℝ) ^ n) ) Filter.atTop (nhds (1 / 2 : ℝ)) := by
      have h5 : Filter.Tendsto (fun (n : ℕ) => (1 / 2 : ℝ) ) Filter.atTop (nhds ( (1 / 2 : ℝ) )) := by 
        simp 
      have h6 : Filter.Tendsto (fun (n : ℕ) => (1 / 2 : ℝ) * ((9 / 11 : ℝ) ^ n) ) Filter.atTop (nhds (0 : ℝ)) := by
        have h7 : Filter.Tendsto (fun (n : ℕ) => ((9 / 11 : ℝ) ^ n) ) Filter.atTop (nhds (0 : ℝ)) := h3 
        have h8 : Filter.Tendsto (fun (n : ℕ) => (1 / 2 : ℝ) ) Filter.atTop (nhds ( (1 / 2 : ℝ) )) := by 
          simp 
        -- Apply limit multiplication rule
        -- Tendsto G * Tendsto H = Tendsto (G * H)
        have h9 : Filter.Tendsto (fun n => (1 / 2 : ℝ) * ((9 / 11 : ℝ) ^ n) ) Filter.atTop (nhds ( (1 / 2 : ℝ) * (0 : ℝ) ) ) := by
          apply Filter.Tendsto.mul
          exact h8
          exact h7 
        -- Simplify result.
        simp at h9 ⊢
        all_goals 
          simpa using h9 
      -- Apply addition rule for limits: `l + 0 = l`
      have h7 : Filter.Tendsto (fun (n : ℕ) => (1 / 2 : ℝ) + (1 / 2 : ℝ) * ((9 / 11 : ℝ) ^ n) ) Filter.atTop (nhds ( (1 / 2 : ℝ) + (0 : ℝ) ) ) := by 
        apply Filter.Tendsto.add 
        exact h5 
        exact h6 
      simp at h7 ⊢ 
      all_goals 
        simpa using h7
    exact h4
  exact h2