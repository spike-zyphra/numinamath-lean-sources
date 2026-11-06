import Mathlib

open Nat

/-19. (CAN 5) The triangular array $\left(a_{n, k}\right)$ of numbers is given by $a_{n, 1}=1 / n$, for $n=1,2, \ldots, a_{n, k+1}=a_{n-1, k}-a_{n, k}$, for $1 \leq k \leq n-1$. Find the harmonic mean of the 1985th row.-/
theorem other_23925 {a : ℕ → ℕ → ℚ} {harm_mean : ℕ → ℚ} (h1 : ∀ n, 1 ≤ n → a n 1 = 1 / n)
(recur : ∀ n k, 1 ≤ n → 1 ≤ k ∧ k ≤ n - 1 → a n (k + 1) = a (n - 1) k - a n k)
(hm : ∀ n, 1 ≤ n → harm_mean n = (n : ℚ) / ∑ i ∈ Finset.range n, 1 / a n (i + 1)) :
harm_mean 1985 = 1 / 2 ^ 1984 := by
-- Prove the following closed formula of $a_n,k$ by induction on $n$ and $k$
  have key : ∀ n, 1 ≤ n → ∀ k, 1 ≤ k ∧ k ≤ n → a n k = 1 / (n * choose (n - 1) (k - 1)) := by
    intro n hn; induction n with
  -- Induction on $n$ first and prove the base cases $n=0$, $n=1$
    | zero => simp_all
    | succ n ihn =>
      by_cases h : n < 1; simp at h
      · simp_all; intro k _ _
        suffices : k = 1; rw [this, h1]; simp
        any_goals linarith
    -- Assume $n$ is greater or equal to $1$, simplify the induction hypothesis
    -- and specialize the recursive relation at $n+1$
      push_neg at h; replace ihn := ihn h
      have tmph1 := recur (n+1); simp at tmph1
      intro k hk; induction k with
    -- Induction on $k$ and prove the base cases $k=0$, $k=1$
      | zero => simp_all
      | succ k ihk =>
        by_cases h' : k < 1; rw [lt_one_iff] at h'; simp_all
      -- Assume $k$ is greater or equal to $1$, simplify the assumptions and prove some simple inequalities
        push_neg at h'; simp at *
        have : k - 1 < k := by exact sub_one_lt_of_lt h'
        replace ihk := ihk h' (show _ by linarith)
        have : 0 < (((n - 1).choose (k - 1)):ℚ) * n := by
          norm_cast; apply Nat.mul_pos
          apply choose_pos; rw [Nat.sub_le_sub_iff_right]
          any_goals linarith
        have : 0 < (n.choose (k - 1):ℚ) * (↑n + 1) := by
          norm_cast; apply Nat.mul_pos
          apply choose_pos; any_goals linarith
      -- Apply the recursive relation tmph1 and two induction hypothesis ihn, ihk to the final goal and simplify
        rw [tmph1, ihn, ihk, sub_eq_iff_eq_add, ← add_mul]; field_simp
        rw [add_mul, one_div_mul_eq_div, one_div_mul_eq_div]; norm_cast
      -- Simplify further by applying two properties of choose functions: Nat.choose_mul and Nat.choose_mul_succ_eq
        have := Nat.choose_mul hk h'; simp at this
        nth_rw 1 [mul_comm, ← this]
        have := Nat.choose_mul_succ_eq (n-1) (k-1)
        rw [show n-1+1=n by rw [Nat.sub_add_cancel]; assumption] at this
        rw [this]; push_cast; repeat rw [mul_div_cancel_left₀]
      -- Finish the rest trivial goals
        repeat rw [Nat.cast_sub]
        ring; any_goals linarith
        any_goals norm_cast; push_neg; rw [Nat.ne_zero_iff_zero_lt]; apply choose_pos
        any_goals linarith
-- Apply the closed formula of $a_n,k$ to rewrite the harmonic mean
  have : ∀ i ∈ Finset.range 1985, 1 / a 1985 (i + 1) = 1985 * (choose 1984 i) := by
    intro i hi; simp at hi; rw [key]; simp
    linarith; constructor; any_goals linarith
  rw [hm, Finset.sum_congr _ this, ← Finset.mul_sum]; push_cast
  simp [div_mul_cancel_left₀]
-- Apply add_pow to finish the final goal
  rw [show (2:ℚ)=1+1 by norm_num, add_pow]; norm_num
  rfl; norm_num