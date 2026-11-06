import Mathlib
/- Suppose that the real numbers $a_{i} \in [-2 ,17], i=1,2, \ldots, 59$, satisfy $a_{1}+a_{2}+\cdots+a_{59}=0$. Prove that

$$
a_{1}^{2}+a_{2}^{2}+\cdots+a_{59}^{2} \leq 2006 .
$$ -/
theorem algebra_241688 (a : ℕ → ℝ) (ha : ∀ i ∈ Finset.range 59, a i ∈ Set.Icc (-2) 17) (hsum : ∑ i in Finset.range 59, a i = 0) :
∑ i in Finset.range 59, (a i) ^ 2 ≤ 2006:= by
    -- Define lower bound m = -2 and upper bound M = 17
    set m:= (-2 : ℝ) with hm
    set M:= (17 : ℝ) with hM
    clear_value m M

    -- Key inequality: For each element, prove (a_i - (m+M)/2)^2 ≤ (M-m)^2/4
    have h1 : ∀ i ∈ Finset.range 59, (a i - (m + M) / 2) ^ 2 ≤ (M - m) ^ 2 / 4:= by
        intro i hi
        specialize ha i hi
        simp at ha
        rcases ha with ⟨h1, h2⟩
        -- Prove a_i - m ≥ 0
        replace h1 : a i - m ≥ 0:= by linarith
        -- Prove M - a_i ≥ 0
        replace h2 : M - a i ≥ 0:= by linarith
        -- Prove their product is non-negative
        have h3 : (M - a i) * (a i - m) ≥ 0:= by positivity
        linarith

    -- Apply the inequality to the sum
    replace h1 : ∑ i in Finset.range 59, (a i - (m + M) / 2) ^ 2 ≤ ∑ i in Finset.range 59, (M - m) ^ 2 / 4:= by exact Finset.sum_le_sum h1
    simp at h1

    -- Expand the squared sum using induction
    have h2 : ∀ n : ℕ, ∑ i in Finset.range n, (a i - (m + M) / 2) ^ 2 = ∑ i in Finset.range n, a i ^ 2 + n * ((m + M) / 2) ^ 2 - (m + M) * ∑ i in Finset.range n, a i:= by
        intro n
        induction n with
        | zero =>
            simp
        | succ n ih =>
            simp [Finset.sum_range_succ]
            rw [ih]
            linarith

    -- Apply the result to n = 59 and use the fact that sum = 0
    specialize h2 59
    rw [hsum] at h2
    subst m M
    norm_num at h1 h2
    linarith
