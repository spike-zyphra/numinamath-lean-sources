import Mathlib

/- 3. A3 (ROM) Let $x_{1}, x_{2}, \ldots, x_{n}$ be arbitrary real numbers.
Prove the inequality  $$ \frac{x_{1}}{1+x_{1}^{2}}+\frac{x_{2}}{1+x_{1}^{2}+x_{2}^{2}}+\cdots+\frac{x_{n}}{1+x_{1}^{2}+\cdots+x_{n}^{2}}<\sqrt{n} $$ -/
theorem inequalities_25088 (n : ℕ) (hn : 0 < n) (x : ℕ → ℝ) :
    ∑ i ∈ Finset.range n,
      x i / (1 + ∑ j ∈ Finset.range (i+1), (x j)^2) < √n := by

  -- by arithmetic-quadratic mean inequality,
  -- if sum (c i)^2 < 1, then sum c i < √n
  have h1 {c: ℕ → ℝ} (h: ∑ i ∈ Finset.range n, (c i)^2 < 1):
    ∑ i ∈ Finset.range n, c i < √n := by
    by_cases h1: ∑ i ∈ Finset.range n, c i < 0
    · apply lt_trans h1 (by simp [hn])
    push_neg at h1
    rw [← sq_lt_sq₀ h1 (by simp), Real.sq_sqrt (by simp)]
    set w: ℕ → ℝ := fun i => 1/n with w_def
    have h2: ∑ i ∈ Finset.range n, c i =
      ∑ i ∈ Finset.range n, (w i * (n * c i )) := by
      apply Finset.sum_congr rfl ?_
      intro _ _; simp [w_def, hn.ne']
    have h3: (∑ i ∈ Finset.range n, w i * (n * c i ))^2 ≤
      ∑ i ∈ Finset.range n, w i * (n * c i)^2 := by
      apply Real.pow_arith_mean_le_arith_mean_pow_of_even _ _ _
        (by simp [w_def]) (by simp [w_def, hn.ne']) (by norm_num)
    rw [h2]
    apply lt_of_le_of_lt h3 ?_
    have h4: ∑ i ∈ Finset.range n, w i * (n * c i)^2 =
      n * ∑ i ∈ Finset.range n, (c i)^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl (fun _ _ => ?_)
      simp only [w_def]
      field_simp [hn.ne']
      ring
    rw [h4]
    apply mul_lt_of_lt_one_right (by simp [hn]) h

  -- then it suffices to show sum (xi/(1+x0^2+..+xi^2))^2 < 1/
  -- consider (xi/(1+x0^2+...+xi^2))^2,
  -- it ≤ xi/(1+x0^2+..+xi^2) xi/(1+x0^2+...+x_{i-1}^2)
  have h2: ∀ i ∈ Finset.range n,
    (x i / (1 + ∑ j ∈ Finset.range (i+1), (x j)^2))^2 ≤
    (1 / (1 + ∑ j ∈ Finset.range i, (x j)^2)) -
    (1 / (1 + ∑ j ∈ Finset.range (i+1), (x j)^2)) := by
    intro i _
    simp only [Finset.sum_range_succ, ← add_assoc]
    -- 1 / a - 1 / (a+b) = b/(a (a+b))
    have h3 {a b: ℝ} (ha: 0 < a) (hb: 0 ≤ b):
      1 / a - 1 / (a+b) = b / (a*(a+b)) := by
      replace hb: 0 < a+b := by linarith only [ha, hb]
      field_simp [ha.ne', hb.ne']
    -- (c/(a+c^2))^2 = c^2 / ((a+c^2)(a+c^)) ≤ c^2 / a(a+c)
    have h4 {a c:ℝ} (ha: 0 < a):
      (c/(a+c^2))^2 ≤ c^2 / (a*(a+c^2)) := by
      rw [div_pow]
      apply div_le_div_of_nonneg_left (sq_nonneg c) ?_ ?_
      · apply mul_pos ha (by linarith only [ha, sq_nonneg c])
      · rw [pow_two (a+c^2)]
        apply mul_le_mul_of_nonneg_right ?_ ?_
        <;> linarith only [ha, sq_nonneg c]
    have ha: 0 < 1 + ∑ j ∈ Finset.range i, (x j)^2 := by
      have: 0 ≤ ∑ j ∈ Finset.range i, (x j)^2 := by
        refine Finset.sum_nonneg' ?_
        simp only [sq_nonneg, implies_true]
      linarith only [this]
    apply (h4 ha).trans (le_of_eq ?_)
    rw [h3 ha (sq_nonneg _)]

  -- and that reduces to 1 - 1/(1+x0^2+...+x_{n-1}^2) < 1
  have h3: ∑ i ∈ Finset.range n, (
      (1 / (1 + ∑ j ∈ Finset.range i, (x j)^2)) -
      (1 / (1 + ∑ j ∈ Finset.range (i+1), (x j)^2))
    ) = 1 - 1 / (1 + ∑ i ∈ Finset.range n, (x i)^2) := by
    replace hn: n ≥ 1 := by exact hn
    clear h1 h2
    induction n,hn using Nat.le_induction
    case base =>
      simp
    case succ n hn ih =>
      nth_rw 1 [Finset.sum_range_succ, ih]
      simp

  -- therefore the problem reduces to 1 - 1/(1+ sum xj^2) < 1, obviously holds.
  apply h1 ?_
  apply lt_of_le_of_lt (Finset.sum_le_sum h2) ?_
  rw [h3]
  simp only [one_div, sub_lt_self_iff, inv_pos]
  apply add_pos_of_pos_of_nonneg (by simp) ?_
  apply Finset.sum_nonneg ?_
  simp only [Finset.mem_range, sq_nonneg, implies_true]