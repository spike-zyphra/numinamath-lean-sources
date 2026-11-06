import Mathlib

/- 13. (20 points) Let real numbers $x_{1}, x_{2}, \cdots, x_{2018}$ satisfy

$$

\begin{array}{l}
x_{n+1}^{2} \leqslant x_{n} x_{n+2} \quad (n=1,2, \cdots, 2016), \\
\prod_{n=1}^{2018} x_{n}=1 .
\end{array}

$$


Prove: $x_{10009} x_{1010} \leqslant 1$. -/
theorem inequalities_272976 (x : ℕ → ℝ) (h1 : ∀ n, x (n + 1) ^ 2 ≤ x n * x (n + 2))
    (h2 : ∏ n ∈ Finset.Icc 1 2018, x n = 1) :
    x 1009 * x 1010 ≤ 1 := by
  -- in the range, x n is not 0, because if it was, product couldn't be 1
  have h3 (n : ℕ) (hn1 : 1 ≤ n) (hn2 : n ≤ 2018) : x n ≠ 0 := by
    by_contra hx
    rw [Finset.prod_eq_zero (show n ∈ Finset.Icc 1 2018 by simp [hn1, hn2]) hx] at h2
    norm_num at h2
  -- assumpe the proeduct is greater than 1, we'll prove contradiction
  by_contra h4
  simp at h4
  -- we'll prove that for n < 1009, 1 < x (1010 - (n + 1)) * x (1009 + (n + 1)) and the expression in rhs is non-decreasing
  have h5 (n : ℕ) (hn : n < 1009) : 1 < x (1010 - (n + 1)) * x (1009 + (n + 1)) ∧
      x (1010 - n) * x (1009 + n) ≤ x (1010 - (n + 1)) * x (1009 + (n + 1)) := by
    -- use strong induction
    induction' n using Nat.strong_induction_on with m hm
    match m with
    -- for 0 obvious
    | 0 =>
      simp
      rw [mul_comm (x 1009)]
      simp
      linarith
    -- for 1, this boils down to proving x 1009 * x 1010 ≤ x 1008 * x 1011, which is true by hypothesis
    | 1 =>
      simp [h4]
      suffices x 1009 * x 1010 ≤ x 1008 * x 1011 by
        simp [this]
        linarith
      have h5 := h1 1008
      have h6 := h1 1009
      simp at h5 h6
      nlinarith
    | k + 2 =>
    -- for k + 2, again we just need to prove 2nd goal x (1010 - (k + 2)) * x (1009 + (k + 2)) ≤ x (1010 - (k + 2 + 1)) * x (1009 + (k + 2 + 1)), 1st goal is implied by that
      have h6 := hm (k + 1) (by omega) (by omega)
      suffices x (1010 - (k + 2)) * x (1009 + (k + 2)) ≤ x (1010 - (k + 2 + 1)) * x (1009 + (k + 2 + 1)) by
        simp at this ⊢
        simp [this]
        replace h6 := h6.left
        simp at h6
        linarith
      -- to prove the goal, we use inductive hypothesis on k, k + 1, from the k, we just need the 1 < ... part and from k + 1, we need the non-decreasing part
      have h5 := h6.left
      replace h6 := h6.right
      -- we also apply problem's hypothesis on following two numbers
      have h7 := h1 (1009 + (k + 1))
      have h8 := h1 (1010 - (k + 3))
      have h11 := (hm k (by omega) (by omega)).left
      -- simplify all expressions, all the expression work with only 6 specific terms
      ring_nf at h5 h6 h7 h8 h11 ⊢
      rw [show 1010 - (1 + k) = 1009 - k by omega] at h6 h11
      rw [show 1010 - (2 + k) = 1008 - k by omega] at h5 h6 ⊢
      rw [show 1010 - (3 + k) = 1007 - k by omega] at h8 ⊢
      rw [show 1 + (1007 - k) = 1008 - k by omega, show 2 + (1007 - k) = 1009 - k by omega] at h8
      -- multiply out the two h1 applications
      have h9 : (x (1008 - k) * x (1011 + k)) * (x (1008 - k) * x (1011 + k)) ≤
          (x (1009 - k) * x (1010 + k)) * (x (1007 - k) * x (1012 + k)) := by
        nlinarith
      -- the lhs can be weakened in last fact to cancel out extra terms and we get our goal
      have h10 : x (1009 - k) * x (1010 + k) * (x (1008 - k) * x (1011 + k)) ≤
          x (1008 - k) * x (1011 + k) * (x (1008 - k) * x (1011 + k)) := by
        gcongr
      replace h10 : x (1009 - k) * x (1010 + k) * (x (1008 - k) * x (1011 + k)) ≤
          (x (1009 - k) * x (1010 + k)) * (x (1007 - k) * x (1012 + k)) := by
        linarith
      nth_rw 2 [mul_comm]
      apply le_of_mul_le_mul_left h10
      linarith
  -- now the reflected product from hypothesis is also 1, multiply the two products which is again 1
  rw [show Finset.Icc 1 2018 = Finset.Ico 1 2019 by rfl] at h2
  have h6 := Finset.prod_Ico_reflect x 1 (show 2019 ≤ 2019 + 1 by norm_num)
  simp at h6
  rw [h2] at h6
  have h7 : (∏ n ∈ Finset.Ico 1 2019, x n) * (∏ n ∈ Finset.Ico 1 2019, x (2019 - n)) = 1 := by nlinarith
  -- pair up the multiplicants, we'll show each of the pair is > 1 so whole product is > 1, contradiction
  rw [← Finset.prod_mul_distrib] at h7
  suffices ∏ n ∈ Finset.Ico 1 2019, 1 < ∏ n ∈ Finset.Ico 1 2019, x n * x (2019 - n) by
    simp at this
    linarith
  apply Finset.prod_lt_prod_of_nonempty
  . simp
  . rintro i hi
    simp at hi
    -- for a pair x i * x (2019 - i), depending on i ≤ 1009 or 1010 ≤ i we can use h5 to show the goal.
    obtain hi' | hi' := le_or_gt i 1009
    . replace h5 := (h5 (1009 - i) (by omega)).left
      convert h5 using 3 <;> omega
    . rw [mul_comm]
      replace h5 := (h5 (1009 + i - 2019) (by omega)).left
      rw [show 1010 - (1009 + i - 2019 + 1) = 2019 - i by omega,
          show 1009 + (1009 + i - 2019 + 1) = i by omega] at h5
      assumption
  . simp