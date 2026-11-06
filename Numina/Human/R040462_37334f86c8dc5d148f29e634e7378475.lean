import Mathlib

/- 24th Australian 2003 Problem B3 The sequence a 1 , a 2 , a 3 , ... has a 1 = 0 and a n+1 = ± (a n + 1) for all n. Show that the arithmetic mean of the first n terms is always at least - ½. -/
theorem inequalities_131615 (a : ℕ → ℝ)
  (h₀ : a 1 = 0)
  (h₁ : ∀ n, a (n + 1) = a n + 1 ∨ a (n + 1) = -(a n + 1)) :
  ∀ n > 0, (1 / n) * ∑ i in Finset.Icc 1 n, a i ≥ -1 / 2 := by
  -- the recursion means a(n+1)^2 = (a(n) + 1)^2
  replace h₁ (n : ℕ) : (a (n + 1))^2 = (a n + 1)^2 := by
    obtain h | h := h₁ n
    all_goals rw [h]
    exact neg_pow_two (a n + 1)
  ring_nf at h₁
  rintro n hn_pos
  -- this means sum over 1 to n is same for a(i+1)^2 and a(i)^2 + 2a(i) + 1
  have h : ∑ i ∈ Finset.Ico 1 (n + 1), (a (i + 1))^2 = ∑ i ∈ Finset.Ico 1 (n + 1), ((a i)^2 + 2 * a i + 1) := by
    rw [Finset.sum_congr rfl]
    rintro i hi
    ring_nf
    exact h₁ i
  -- manipulate to turn the lhs to a(n+1)^2 +  sum over 1 to n of a(i)^2
  have h' : ∑ i ∈ Finset.Ico 1 (n + 1), (a (i + 1))^2 =  ∑ i ∈ Finset.Ico 1 (n + 1), (a i)^2 + (a (n + 1))^2 := by
    rw [Finset.sum_Ico_succ_top (by linarith)]
    nth_rw 2 [Finset.sum_eq_sum_Ico_succ_bot (by linarith)]
    rw [h₀]
    rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    congr
    ring_nf
    rw [show n + 1 -2 = n - 1 by omega]
    ring
  rw [h'] at h
  repeat rw [Finset.sum_add_distrib] at h
  -- so we can cancel the sum of squares from both sides
  replace h : (a (n + 1))^2 = ∑ x ∈ Finset.Ico 1 (n + 1), 2 * a x + ∑ x ∈ Finset.Ico 1 (n + 1), 1 := by linarith
  -- this means a(n+1)^2 = 2 * sum of a(i) for i = 1..n + n
  simp at h
  rw [← Finset.mul_sum] at h
  change a (n + 1) ^ 2 = 2 * ∑ i ∈ Finset.Icc 1 n, a i + n at h
  -- due to square being nonnegative, we have target sum * 2 + n >= 0, from this we get result easily
  replace h' : 0 ≤ 2 * ∑ i ∈ Finset.Icc 1 n, a i + n := by
    rw [← h]
    positivity
  replace h' : -n / 2 ≤ ∑ i ∈ Finset.Icc 1 n, a i := by linarith
  replace h' : (-n / 2) / n ≤ (∑ i ∈ Finset.Icc 1 n, a i) / n := by gcongr
  rw [show (- n / 2 : ℝ) / n = -1 / 2 by field_simp; ring_nf] at h'
  linear_combination h'