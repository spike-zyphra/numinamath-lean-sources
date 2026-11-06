import Mathlib

/- Find the maximum positive integer $k$ such that for any positive integers $m, n$ such that $m^{3}+n^{3}>$ $(m+n)^{2}$, we have

$$
m^{3}+n^{3} \geq(m+n)^{2}+k
$$ -/
theorem inequalities_604925 :
  IsGreatest {k : ℤ| ∀ m n : ℤ, 0 < m ∧ 0 < n ∧ (m + n)^2 < m^3 + n^3 →
  (m + n)^2 + k ≤ m^3 + n^3} 10 := by
    constructor
    · simp
      -- We will show that $k=10$ is the desired maximum. In other words, we have to prove that
      -- $$
      -- m^{3}+n^{3} \geq(m+n)^{2}+10
      -- $$
      intro m n mpos npos h1
      -- The last inequality is equivalent to
      -- $$
      -- (m+n)\left(m^{2}+n^{2}-m n-m-n\right) \geq 10
      -- $$
      suffices 10 ≤ (m + n) * (m^2 + n^2 - m*n - m - n) by nlinarith
      have h2 : 2 ≤ m + n := by omega
      by_cases h3 : 5 ≤ m + n
      · -- If $m+n \geq 5$ then we will show that
        -- $$
        -- m^{2}+n^{2}-m n-m-n \geq 2
        -- $$
        have : 2 ≤ m ^ 2 + n ^ 2 - m * n - m - n := by
          -- which is equivalent to
          -- $$
          -- (m-n)^{2}+(m-1)^{2}+(n-1)^{2} \geq 6
          -- $$
          suffices 6 ≤  (m - n)^2 + (m - 1)^2 + (n - 1)^2 by nlinarith
          by_cases hmn : 4 ≤ m ∨ 4 ≤ n
          · -- If at least one of the numbers $m, n$ is greater or equal to 4 then $(m-1)^{2} \geq 9$ or $(n-1)^{2} \geq 9$ hence the desired result holds. 
            rcases hmn with hm | hn <;> nlinarith
          · simp at hmn
            obtain ⟨hm, hn⟩ := hmn
            -- As a result, it remains to check what happens if $m \leq 3$ and $n \leq 3$. Using the condition $m+n \geq 5$ we have that all such pairs are $(m, n)=(2,3),(3,2),(3,3)$.
            have h4 : (m, n) = (2, 3) ∨ (m, n) = (3, 2) ∨ (m, n) = (3, 3) := by
              interval_cases m <;> interval_cases n <;> tauto
            simp at h4
            -- All of them satisfy the condition and also the inequality $m^{2}+n^{2}-m n-m-n \geq 2$, thus we have the desired result.
            rcases h4 with h | h | h <;> simp [h]
        calc
          _ = 5 * (2 : ℤ):= rfl
          _ ≤ _ := mul_le_mul h3 this (by omega) (by omega)
      · simp at h3
        -- If $m+n=2$ or $m+n=3$ or $m+n=4$, then $(m, n)=(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)$ and we can check that none of them satisfies the condition 
        have hmn : (m, n) = (1, 1) ∨ (m, n) = (1, 2) ∨ (m, n) = (1, 3) ∨ (m, n) = (2, 1)
        ∨ (m, n) = (2, 2) ∨ (m, n) = (3, 1) := by
          have : 1 ≤ m := by omega
          have : m < 4 := by omega
          have : 1 ≤ n := by omega
          interval_cases m
          · have : n < 4 := by omega
            interval_cases n <;> simp
          · have : n < 3 := by omega
            interval_cases n <;> simp
          · have : n < 2:= by omega
            interval_cases n; simp
        rcases hmn with h | h | h | h | h |h <;> simp at h <;> simp [h] at h1 ⊢
    · -- We see that for $m=3$ and $n=2$ we have $m^{3}+n^{3}>(m+n)^{2}$, thus
      -- $$
      -- 3^{3}+2^{3} \geq(3+2)^{2}+k \Rightarrow k \leq 10
      -- $$
      simp [upperBounds]
      intro k h
      specialize h 3 2
      simp at h
      linarith
