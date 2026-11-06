import Mathlib

/-Define the sequence $\left\{x_{i}\right\}_{i \geq 0}$ by $x_{0}=x_{1}=x_{2}=1$ and $x_{k}=\frac{x_{k-1}+x_{k-2}+1}{x_{k-3}}$ for $k>2$. Find $x_{2013}$.-/
theorem algebra_609199 (x : ℕ → ℝ) (h0 : x 0 = 1) (h1 : x 1 = 1) (h2 : x 2 = 1) (hk : ∀ k > 2, x k = (x (k - 1) + x (k - 2) + 1) / x (k - 3)) :
    x 2013 = 9 := by
  -- show that x 3 = 3
  have h3 : x 3 = 3 := by
    rw [hk 3]
    norm_num
    rw [h0, h1, h2]
    all_goals norm_num
  -- show that x 4 = 5
  have h4 : x 4 = 5 := by
    rw [hk 4]
    norm_num
    rw [h3, h1, h2]
    all_goals norm_num
  -- show that x 5 = 9
  have h5 : x 5 = 9 := by
    rw [hk 5]
    norm_num
    rw [h3, h4, h2]
    all_goals norm_num
  -- show that x 6 = 5
  have h6 : x 6 = 5 := by
    rw [hk 6]
    norm_num
    rw [h3, h4, h5]
    all_goals norm_num
  -- show that x 7 = 3
  have h7 : x 7 = 3 := by
    rw [hk 7]
    norm_num
    rw [h6, h4, h5]
    all_goals norm_num
  -- show that x 8 = 1
  have h8 : x 8 = 1 := by
    rw [hk 8]
    norm_num
    rw [h5, h6, h7]
    all_goals norm_num
  -- show that x has period 8
  have period (k : ℕ) : x (k + 8) = x k := by
    -- show that x 9 = 1
    have h9 : x 9 = 1 := by
      rw [hk 9]
      norm_num
      rw [h8, h6, h7]
      all_goals norm_num
    -- show that x 10 = 1
    have h10 : x 10 = 1 := by
      rw [hk 10]
      norm_num
      rw [h9, h7, h8]
      all_goals norm_num

    -- prove the conclusion by three step induction
    have period (k : ℕ) : x (k + 8) = x k ∧ x (k + 9) = x (k + 1) ∧ x (k + 10) = x (k + 2) := by
      -- prove by induction
      induction k with
      | zero => -- when k = 0
        norm_num
        rw [h8, h9, h10, h0, h1, h2]
        norm_num
      | succ k hk' => -- when k > 0
        ring_nf at hk' ⊢
        -- get the proposition of 0 ≤ k
        have hle : 0 ≤ k := by
          positivity
        -- rewrite by hk
        have hk11 : x (11 + k) = x (3 + k) := by
          -- use the recursive formula of 11 + k
          rw [hk (11 + k)]
          repeat rw [Nat.sub_add_comm]
          norm_num
          -- use the induction hypothesis
          rw [hk'.1, hk'.2.1, hk'.2.2]
          -- use the recursive formula of 3 + k
          rw [hk (3 + k)]
          repeat rw [Nat.sub_add_comm]
          norm_num
          -- show the condition
          all_goals norm_num
          all_goals linarith only [hle]
        tauto
    replace period := period k
    tauto

  replace period (k : ℕ) (t : ℕ) : x (k + 8 * t) = x k := by
    -- prove by induction of t
    induction t with
    | zero => -- when t = 0
      norm_num
    | succ t ht => -- when t > 0
      calc
        x (k + 8 * (t + 1)) = x (k + 8 * t + 8) := by ring_nf
        _ = x (k + 8 * t) := by rw [period (k + 8 * t)]
        _ = x k := by rw [ht]
  -- show that x 2013 = 9
  rw [<-h5, <-period 5 251]