import Mathlib
/- II. (50 points) The sequence $\left\{a_{n}\right\}$ is defined as follows: $a_{1}=\frac{1}{2}$, and $a_{n+1}=\frac{a_{n}^{2}}{a_{n}^{2}-a_{n}+1}, n=1,2, \cdots$. Prove: For every positive integer $n$, we have $a_{1}+a_{2}+\cdots+a_{n}<1$.

保留源文本的换行和格式，翻译结果如下：

II. (50 points) The sequence $\left\{a_{n}\right\}$ is defined as follows: $a_{1}=\frac{1}{2}$, and $a_{n+1}=\frac{a_{n}^{2}}{a_{n}^{2}-a_{n}+1}, n=1,2, \cdots$. Prove: For every positive integer $n$, we have $a_{1}+a_{2}+\cdots+a_{n}<1$. -/
theorem number_theory_275765 (a : ℕ → ℝ) (h1 : a 0 = 1 / 2) (h : ∀ n : ℕ, a (n + 1) = a n ^ 2 / (a n ^ 2 - a n + 1)) : ∀ n : ℕ, ∑ i in Finset.range n, a i < 1:= by
  -- First, prove that all terms in the sequence are positive
  have hpos : ∀ n : ℕ, a n > 0:= by
    intro n
    induction n with
    | zero =>
      -- Base case: a_0 = 1/2 > 0
      rw [h1]
      simp
    | succ n ih =>
      -- Inductive step: if a_n > 0, then a_{n+1} > 0
      rw [h n]
      -- Rewrite the denominator to show it's positive
      rw [show a n ^ 2 - a n + 1 = (a n - 1 / 2) ^ 2 + 3 / 4 by ring_nf]
      positivity
  -- Next, prove that the sequence is decreasing
  have hle : ∀ n : ℕ, a (n + 1) ≤ a n:= by
    intro n
    rw [h n]
    -- Show that the denominator is positive
    have g : a n ^ 2 - a n + 1 > 0:= by
      suffices (a n - 1 / 2) ^ 2 + 3 / 4 > 0 by linarith
      positivity
    -- Use division inequality to show a_{n+1} ≤ a_n
    suffices a n ^ 2 ≤ a n * (a n ^ 2 - a n + 1) by exact (div_le_iff₀ g).mpr this
    -- This simplifies to showing a_n * (a_n - 1)^2 ≥ 0
    suffices a n * (a n - 1) ^ 2 ≥ 0 by linarith
    specialize hpos n
    positivity
  intro n
  -- Prove that all terms are less than 1
  have h2 : ∀ i : ℕ, a i < 1:= by
    intro i
    induction i with
    | zero =>
      -- Base case: a_0 = 1/2 < 1
      rw [h1]
      linarith
    | succ i ih =>
      -- Since the sequence is decreasing and a_i < 1, we have a_{i+1} < 1
      specialize hle i
      linarith
  -- Key insight: express each term as a telescoping difference
  have h3 : ∀ i : ℕ, a i = 1 / (1 / a i - 1) - 1 / (1 / a (i + 1) - 1):= by
    intro i
    have g1:= h2 i
    specialize h i
    specialize hpos i
    -- Transform the recurrence relation to get the telescoping form
    replace h : 1 / a (i + 1) - 1 = (1 - a i) / a i ^ 2:= by
      rw [h]
      field_simp
      ring_nf
    rw [h]
    field_simp
    replace g1 : 1 - a i > 0:= by linarith
    field_simp
    ring_nf
  -- Use telescoping sum to get a closed form for the partial sums
  have h4 : ∀ n : ℕ, ∑ i in Finset.range n, a i = 1 / (1 / a 0 - 1) - 1 / (1 / a n - 1):= by
    intro n
    induction n with
    | zero =>
      -- Base case: empty sum equals 0
      simp
    | succ n ih =>
      -- Inductive step: use the telescoping property
      rw [Finset.sum_range_succ, ih]
      specialize h3 n
      linarith
  -- Apply the telescoping sum formula
  rw [h4 n]
  rw [h1]
  -- Show that 1 / a_n - 1 > 0 (needed for positivity)
  have g1 : 1 / a n - 1 > 0:= by
    specialize hpos n
    specialize h2 n
    field_simp
    exact h2
  -- Simplify 1 / (1 / (1/2) - 1) = 1 / (2 - 1) = 1
  rw [show 1 / (1 / ((1 : ℝ) / 2) - 1) = 1 by norm_num]
  -- Since 1 / (1 / a_n - 1) > 0, we have 1 - 1 / (1 / a_n - 1) < 1
  suffices 1 / (1 / a n - 1) > 0 by linarith
  positivity
