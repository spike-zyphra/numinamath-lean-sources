import Mathlib

open Finset

/- Let $\left(a_{n}\right)$ be the sequence defined by $a_{1}=1$ and $a_{n+1}=1+a_{1} a_{2} \ldots a_{n}$. Determine $\sum_{n=1}^{+\infty} \frac{1}{a_{n}}$. -/
theorem number_theory_151527 (a : ℕ → ℝ)
    (h₀ : a 0 = 1)
    (h₁ : ∀ n, a (n + 1) = 1 + ∏ i ∈ range (n + 1), a i) :
    ∑' n, 1 / a n = 2 := by
  -- Prove that 1 < a i for all i ≠ 0.
  have ha1 i (hi : 0 < i) : 1 < a i := by
    -- Proof by strong induction.
    induction' i using Nat.strongRec with i ih
    -- Consider two cases: i = 0 and i > 0.
    cases i with
    | zero => contradiction
    | succ i =>
      -- Suppose that m < i + 1 and 0 < m implies 1 < a m and prove that 1 < a (i + 1).
      -- We have a (i + 1) = 1 + ∏ k ∈ [0, i], a k so it is enough to show that 0 < ∏ i ∈ [0, i], a k.
      nth_rw 1 [h₁, ← add_zero 1]
      gcongr
      apply Finset.prod_pos
      simp only [mem_range]
      -- It is left to prove that 0 < a j for all j ≤ i.
      intro j hj
      cases j with
      -- If j = 0 then a 0 = 1 > 0.
      | zero => simp [h₀]
      -- If j > 0 then a j > 1 > 0 (by the induction hypothesis).
      | succ j => linarith [ih (j + 1) hj (by omega)]
  -- We also have 0 < a i for all i.
  have ha0 i : 0 < a i := by
    cases i with
    | zero => simp [h₀]
    | succ i => linarith [ha1 (i + 1) (by omega)]
  -- Show that a(i + 1) = 1 + a(i) * (a(i) - 1) for all i ≠ 0.
  have ha i (hi : 0 < i) : a (i + 1) = 1 + a i * (a i - 1) := by
    cases i with
    | zero => contradiction
    | succ i =>
      -- We have a(i + 2) = 1 + ∏ j ∈ [0, i + 1], a j
      --                  = 1 + a (i + 1) * ∏ j ∈ [0, i], a j
      --                  = 1 + a (i + 1) * (a(i + 1) - 1).
      rw [h₁, prod_range_succ, mul_comm]
      congr
      rw [h₁]
      ring
  -- Prove that a(i) is unbounded. More specifically, i + 1 ≤ a(i) for all i.
  have ha_unbounded i : i + 1 ≤ a i := by
    -- Proof by induction.
    induction i with
    -- If i = 0 then 0 + 1 ≤ 1 = a(0).
    | zero => simp [h₀]
    | succ i ih =>
      -- Suppose that i + 1 ≤ a(i) and show that (i + 1) + 1 ≤ a(i + 1).
      cases i with
      -- If i = 0 then 2 ≤ a(1).
      | zero => simp [h₁, h₀]
      | succ i =>
        -- If i = j + 1 then a(i + 1) = a(j + 2) = 1 + a(j + 1) * (a(j + 1) - 1).
        -- We know that (j + 1) + 1 ≤ a(j + 1) so
        -- 1 + a(j + 1) * (a(j + 1) - 1) ≥ 1 + (j + 2) * (j + 1) ≥ j + 3 = i + 2.
        rw [ha (i + 1) (by omega)]
        push_cast at ih ⊢
        nlinarith
  -- Show that the following equality holds for 1 ≤ i:
  -- 1 / a(i) = 1 / (a(i) - 1) - 1 / (a(i + 1) - 1).
  replace ha {i} (hi : 1 ≤ i): 1 / a i = 1 / (a i - 1) - 1 / (a (i + 1) - 1) := by
    have h0 k : a (i + k) - 1 ≠ 0 := by apply ne_of_gt; linarith [ha1 (i + k) (by omega)]
    -- Simplify this equality and get (a(i) - 1) * (a(i + 1) - 1) = (a(i + 1) - a(i)) * a(i).
    field_simp [add_zero i ▸ h0 0, h0 1, show a i ≠ 0 from ne_of_gt (ha0 i)]
    -- We know that a(i + 1) = 1 + a(i) * (a(i) - 1).
    -- Make this substitution and simplify the expression to get the result.
    rw [ha i (by omega)]
    ring
  -- Rewrite the theorem statement in terms of HasSum
  suffices HasSum (fun n : ℕ => 1 / a n) 2 from this.tsum_eq
  -- Rewrite the theorem statement as
  -- Filter.Tendsto (fun n ↦ ∑ i ∈ range n, 1 / a n) Filter.atTop (nhds 2))
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun i => one_div_nonneg.mpr <| le_of_lt <| ha0 i)]
  -- Show that ∑ i ∈ range n, 1 / a i = 2 - 1 / (a n - 1) for all n ≥ 1.
  have hsum {n} (hn : 1 ≤ n) : ∑ i ∈ range n, 1 / a i = 2 - 1 / (a n - 1) := calc
    -- We have ∑ i ∈ range n, 1 / a(i) = 1 / a(0) + ∑ i ∈ range (n - 1), 1 / a (i + 1).
    ∑ i ∈ range n, 1 / a i = 1 + ∑ i ∈ range (n - 1), 1 / a (i + 1) := by
        nth_rw 1 [show n = (n - 1) + 1 by omega, sum_range_succ', h₀, add_comm, div_one]
    -- Use ha to rewrite this sum as 1 + ∑ i ∈ range (n - 1), (1 / (a (i + 1) - 1) - 1 / (a (i + 2) - 1)).
    _ = 1 + ∑ i ∈ range (n - 1), (1 / (a (i + 1) - 1) - 1 / (a (i + 2) - 1)) := by
        congr 1
        apply sum_congr rfl
        intro i hi
        rw [ha (by omega)]
    -- After cancelling terms in the sum, we get 1 + 1 / (a(1) - 1) - 1 / (a(n) - 1) = 1 + 1 - 1 / (a(n) - 1).
    _ = 1 + 1 / (a 1 - 1) - 1 / (a n - 1) := by
        rw [sum_range_sub', show n - 1 + 1 = n by omega, zero_add, add_sub_assoc]
    _ = 2 - 1 / (a n - 1) := by
        simp [h₁, h₀]
        norm_num
  -- We get that the sum ∑ i ∈ range n, 1 / a i is eventually equal to 2 - 1 / (a(n) - 1).
  have hsum' : (fun n => 2 - 1 / (a n - 1)) =ᶠ[.atTop] (fun n => ∑ i ∈ range n, 1 / a i) := by
    simp_rw [Filter.EventuallyEq, Filter.eventually_atTop]
    use 1
    intro n hn
    rw [hsum hn]
  -- It is left to find the limit of 2 - 1 / (a(n) - 1) as n tends to infinity.
  apply Filter.Tendsto.congr' hsum'
  nth_rw 2 [← sub_zero 2]
  apply Filter.Tendsto.const_sub
  -- Show that lim (1 / (a(n) - 1)) = 0 as n tends to infinity.
  rw [NormedAddCommGroup.tendsto_atTop]
  -- We need to show that for any e > 0 there exists N such that |1 / (a(i) - 1)| < e
  -- for all i ≥ N.
  intro e he
  simp only [sub_zero, norm_inv, Real.norm_eq_abs]
  -- Find n such 1 / e ≤ n.
  have ⟨n, hn⟩ := exists_nat_ge (1 / e)
  -- Take N = n + 1.
  use n + 1
  intro i hni
  -- We have 1 < a(i) for i ≥ N = n + 1.
  have ineq1 := ha1 i (by omega)
  -- We have i + 1 ≤ a(i) for i ≥ N.
  have ineq2 := ha_unbounded i
  -- It follows that 0 ≤ 1 / (a(i) - 1).
  have hnonneg : 0 ≤ 1 / (a i - 1) := by apply div_nonneg zero_le_one; linarith
  rw [abs_of_nonneg hnonneg, one_div_lt (by linarith) he]
  -- It is left to show that 1 / e < a(i) - 1.
  -- This inequality follows from 1 / e < n < i ≤ a(i) - 1.
  rify at hni
  linarith