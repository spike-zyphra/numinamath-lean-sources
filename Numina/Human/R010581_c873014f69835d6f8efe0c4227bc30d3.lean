import Mathlib
/- 3. A3 (GRE) Let $a>2$ be given, and define recursively  $$ a_{0}=1, \quad a_{1}=a, \quad a_{n+1}=\left(\frac{a_{n}^{2}}{a_{n-1}^{2}}-2\right) a_{n} $$  Show that for all $k \in \mathbb{N}$, we have  $$ \frac{1}{a_{0}}+\frac{1}{a_{1}}+\frac{1}{a_{2}}+\cdots+\frac{1}{a_{k}}<\frac{1}{2}\left(2+a-\sqrt{a^{2}-4}\right) . $$ -/
theorem algebra_24719 (a : ℕ → ℝ) (c : ℝ) (hc : c > 2) (ha0 : a 0 = 1) (ha1 : a 1 = c) (han : ∀ n : ℕ, a (n + 2) = (a (n + 1) ^ 2 / a n ^ 2 - 2) * a (n + 1)) : ∀ k : ℕ, ∑ i in Finset.range (k + 1), (1 / a i) < 1 / 2 * (2 + c - √(c ^ 2 - 4)):= by
  -- show that for b = (c + √(c ^ 2 - 4)) / 2, we have a 1 = b + b⁻¹
  have h1 : ∃ b > 0, c = b + b⁻¹ ∧ b = (c + √(c ^ 2 - 4)) / 2:= by
    use (c + √(c ^ 2 - 4)) / 2
    simp
    constructor
    -- show b > 0 by positivity
    .
      positivity
    -- use the lemma √x ^ 2 = x for x ≥ 0 to show a 1 = b + b⁻¹
    .
      field_simp
      ring_nf
      have hcpos : c ^ 2 > 2 ^ 2:= by nlinarith [hc]
      replace hcpos : -4 + c ^ 2 > 0:= by nlinarith
      rw [show √(-4 + c ^ 2) ^ 2 = -4 + c ^ 2 by refine Real.sq_sqrt (by linarith)]
      linarith
  rcases h1 with ⟨b, hbpos, h1, hb1⟩
  rw [h1] at ha1
  -- show by induction that a n > 0 and a n = b ^ (2 ^ n) + (b⁻¹) ^ (2 ^ n) forall n ≥ 0
  have h2 : ∀ n : ℕ, (a (n + 1) / a n = b ^ (2 ^ n) + (b⁻¹) ^ (2 ^ n)) ∧ a (n + 1) > 0:= by
    intro n
    induction n with
    -- base case is proved by simp and positivity
    | zero =>
      simp [ha0, ha1]
      positivity
    | succ n ih =>
    -- we show that a (n + 2) / a (n + 1) = (a (n + 1) / a n) ^ 2 - 2
      rw [show n + 1 + 1 = n + 2 by omega]
      specialize han n
      rcases ih with ⟨ih1, ih2⟩
      -- use the induction hypothesis
      replace han : a (n + 2) / a (n + 1) = (a (n + 1) ^ 2 / a n ^ 2 - 2):= by
        field_simp
        exact han
      constructor
      .
        rw [han]
        rw [show a (n + 1) ^ 2 / a n ^ 2 = (a (n + 1) / a n) ^ 2 by ring]
        rw [ih1]
        ring_nf
        field_simp
      .
        -- show that a (n + 1) ^ 2 / a n ^ 2 - 2 = b ^ 2 ^ (n + 1) + b⁻¹ ^ 2 ^ (n + 1) > 0
        rw [show a (n + 1) ^ 2 / a n ^ 2 = (a (n + 1) / a n) ^ 2 by ring] at han
        rw [ih1] at han
        have g1 : (b ^ 2 ^ n + b⁻¹ ^ 2 ^ n) ^ 2 - 2 = b ^ 2 ^ (n + 1) + b⁻¹ ^ 2 ^ (n + 1):= by
          ring_nf
          rw [show b ^ 2 ^ n * b⁻¹ ^ 2 ^ n = (b * b⁻¹) ^ 2 ^ n by exact Eq.symm (mul_pow b b⁻¹ (2 ^ n))]
          field_simp
        -- so a (n + 2) / a (n + 1) > 0 and a (n + 1) > 0, we get a (n + 2) > 0
        rw [g1] at han
        have g2 : b ^ 2 ^ (n + 1) + b⁻¹ ^ 2 ^ (n + 1) > 0:= by positivity
        rw [←han] at g2
        field_simp at g2
        exact g2
  -- get from h2 that a n > 0 for all n ≥ 0
  have h3 : ∀ n : ℕ, a n > 0:= by
    intro n
    by_cases h : n = 0
    -- the n = 0 case is proved by simp
    .
      subst n
      simp [ha0]
    .
      replace h : n > 0:= by omega
      specialize h2 (n - 1)
      replace h2:= h2.2
      rw [show n - 1 + 1 = n by omega] at h2
      exact h2
  -- get from h2 that a (n + 1) = b ^ (2 ^ n) + (b⁻¹) ^ (2 ^ n) for all n ≥ 0
  replace h2 : ∀ n : ℕ, a (n + 1) / a n = b ^ (2 ^ n) + (b⁻¹) ^ (2 ^ n):= by simp [h2]
  -- show by induction that 1 / a (n + 1) = b ^ (2 ^ (n + 1) - 1) / (∏ i in Finset.range (n + 1), (b ^ (2 ^ (i + 1)) + 1)) for all n ≥ 0
  have h4 : ∀ n : ℕ, 1 / a (n + 1) = b ^ (2 ^ (n + 1) - 1) / (∏ i in Finset.range (n + 1), (b ^ (2 ^ (i + 1)) + 1)):= by
    intro n
    induction n with
    -- the n = 0 case is proved by simp and field_simp
    | zero =>
      simp [ha1]
      field_simp
      left
      ring
    -- for the n + 1 case, we use the induction hypothesis and h2 (n + 1)
    | succ n ih =>
      rw [show n + 1 + 1 = n + 2 by omega]
      specialize h2 (n + 1)
      rw [show n + 1 + 1 = n + 2 by omega] at h2
      replace h2 : 1 / a (n + 2) = (1 / a (n + 1)) / (b ^ 2 ^ (n + 1) + b⁻¹ ^ 2 ^ (n + 1)):= by
        have g1:= h3 (n + 1)
        have g2:= h3 (n + 2)
        -- we need the positivity of denominators to use field_simp
        field_simp
        field_simp at h2
        linarith only [h2]
      rw [h2, ih]
      -- use the Finset.prod_range_succ theorem
      simp [Finset.prod_range_succ]
      field_simp
      ring_nf
      -- introduce a variable t to simplify the expression
      let t:= (∏ x ∈ Finset.range n, (b ^ 2 ^ (x + 1) + 1))
      have ht : t = (∏ x ∈ Finset.range n, (b ^ 2 ^ (x + 1) + 1)):= by rfl
      clear_value t
      rw [←ht]
      -- refine the expression and finish the proof
      rw [show b ^ (2 ^ n * 2 - 1) * b ^ (2 ^ n * 2) * (t * (1 + b ^ (2 ^ n * 2)) * (1 + b ^ (2 ^ n * 4))) = b ^ (2 ^ n * 2 - 1) * b ^ (2 ^ n * 2) * (1 + b ^ (2 ^ n * 2)) * (1 + b ^ (2 ^ n * 4)) * t by ring]
      rw [show b ^ (2 ^ n * 4 - 1) * (t * (1 + b ^ (2 ^ n * 2)) * (1 + b ^ (2 ^ n * 4))) = b ^ (2 ^ n * 4 - 1) * (1 + b ^ (2 ^ n * 2)) * (1 + b ^ (2 ^ n * 4)) * t by ring]
      suffices b ^ (2 ^ n * 2 - 1) * b ^ (2 ^ n * 2) * (1 + b ^ (2 ^ n * 2)) * (1 + b ^ (2 ^ n * 4)) = b ^ (2 ^ n * 4 - 1) * (1 + b ^ (2 ^ n * 2)) * (1 + b ^ (2 ^ n * 4)) by rw [this]
      rw [show b ^ (2 ^ n * 2 - 1) * b ^ (2 ^ n * 2) = b ^ (2 ^ n * 2 - 1 + 2 ^ n * 2) by exact Eq.symm (pow_add b (2 ^ n * 2 - 1) (2 ^ n * 2))]
      rw [show (2 ^ n * 2 - 1) + 2 ^ n * 2 = 2 ^ n * 4 - 1 by omega]
  -- rewrite the expression of 1 / a (n + 1) as (1 / b) * (d (n + 1) - d n) form
  have h5 : ∀ n : ℕ, b ^ (2 ^ (n + 1) - 1) / ∏ i ∈ Finset.range (n + 1), (b ^ 2 ^ (i + 1) + 1) = (1 / b) * (1 / ∏ i ∈ Finset.range n, (b ^ 2 ^ (i + 1) + 1) - 1 / ∏ i ∈ Finset.range (n + 1), (b ^ 2 ^ (i + 1) + 1)):= by
    intro n
    -- extract the 1 / b factor
    have g1 : b ^ (2 ^ (n + 1) - 1) = (1 / b) * (b ^ (2 ^ (n + 1))):= by
      field_simp
      rw [show b ^ (2 ^ (n + 1) - 1) * b = b ^ (2 ^ (n + 1) - 1 + 1) by exact rfl]
      have _ : 2 ^ (n + 1) > 0:= by exact Nat.two_pow_pos (n + 1)
      rw [show 2 ^ (n + 1) - 1 + 1 = 2 ^ (n + 1) by omega]
    rw [g1]
    -- write b ^ 2 ^ (n + 1) as b ^ 2 ^ (n + 1) + 1 - 1 and split the fraction

    rw [show 1 / b * b ^ 2 ^ (n + 1) / ∏ i ∈ Finset.range (n + 1), (b ^ 2 ^ (i + 1) + 1) = 1 / b * (b ^ 2 ^ (n + 1) / ∏ i ∈ Finset.range (n + 1), (b ^ 2 ^ (i + 1) + 1)) by ring]
    suffices (b ^ 2 ^ (n + 1) / ∏ i ∈ Finset.range (n + 1), (b ^ 2 ^ (i + 1) + 1)) = (1 / ∏ i ∈ Finset.range n, (b ^ 2 ^ (i + 1) + 1) - 1 / ∏ i ∈ Finset.range (n + 1), (b ^ 2 ^ (i + 1) + 1)) by rw [this]
    rw [show b ^ 2 ^ (n + 1) = b ^ 2 ^ (n + 1) + 1 - 1 by ring]
    rw [show (b ^ 2 ^ (n + 1) + 1 - 1) / ∏ i ∈ Finset.range (n + 1), (b ^ 2 ^ (i + 1) + 1) = (b ^ 2 ^ (n + 1) + 1) / ∏ i ∈ Finset.range (n + 1), (b ^ 2 ^ (i + 1) + 1) - 1 / ∏ i ∈ Finset.range (n + 1), (b ^ 2 ^ (i + 1) + 1) by ring]
    -- apply Finset.prod_range_succ theorem to finish the proof
    suffices (b ^ 2 ^ (n + 1) + 1) / ∏ i ∈ Finset.range (n + 1), (b ^ 2 ^ (i + 1) + 1) = 1 / ∏ i ∈ Finset.range n, (b ^ 2 ^ (i + 1) + 1) by rw [this]
    simp [Finset.prod_range_succ]
    field_simp
    ring
  intro k
  -- extract 1 / a 0 = 1 and rewrite the sum as 1 + ∑ i ∈ Finset.range k, 1 / a (i + 1) by induction
  have h6 : ∀ n : ℕ, ∑ i ∈ Finset.range (n + 1), 1 / a i = 1 + ∑ i ∈ Finset.range n, 1 / a (i + 1):= by
    intro m
    induction m with
    -- the m = 0 case is proved by simp
    | zero =>
      simp [ha0]
    -- for the m + 1 case, we use the induction hypothesis and the sum_range_succ theorem
    | succ m ih =>
      rw [show m + 1 + 1 = m + 2 by omega]
      simp [Finset.sum_range_succ] at ih
      simp [Finset.sum_range_succ]
      linarith
  specialize h6 k
  rw [h6]
  clear h6
  -- show that ∑ 1 / a (i + 1) = (1 / b) * ∑ (d (i + 1) - d i)
  replace h4 : ∀ i ∈ Finset.range k, 1 / a (i + 1) = 1 / b * (1 / ∏ i ∈ Finset.range i, (b ^ 2 ^ (i + 1) + 1) - 1 / ∏ i ∈ Finset.range (i + 1), (b ^ 2 ^ (i + 1) + 1)):= by
    intro i _
    specialize h4 i
    specialize h5 i
    rw [h5] at h4
    exact h4
  replace h5 : ∑ i ∈ Finset.range k, 1 / a (i + 1) = ∑ i ∈ Finset.range k, (1 / b * (1 / ∏ i ∈ Finset.range i, (b ^ 2 ^ (i + 1) + 1) - 1 / ∏ i ∈ Finset.range (i + 1), (b ^ 2 ^ (i + 1) + 1))):= Finset.sum_congr rfl h4
  have h6 : ∑ i ∈ Finset.range k, (1 / b * (1 / ∏ i ∈ Finset.range i, (b ^ 2 ^ (i + 1) + 1) - 1 / ∏ i ∈ Finset.range (i + 1), (b ^ 2 ^ (i + 1) + 1))) = (1 / b) * ∑ i ∈ Finset.range k, (1 / ∏ i ∈ Finset.range i, (b ^ 2 ^ (i + 1) + 1) - 1 / ∏ i ∈ Finset.range (i + 1), (b ^ 2 ^ (i + 1) + 1)):= Eq.symm
      (Finset.mul_sum (Finset.range k)
        (fun i =>
          1 / ∏ i ∈ Finset.range i, (b ^ 2 ^ (i + 1) + 1) -
            1 / ∏ i ∈ Finset.range (i + 1), (b ^ 2 ^ (i + 1) + 1))
        (1 / b))
  -- show by induction that ∑ (d (i + 1) - d i) = 1 - 1 / ∏ i ∈ Finset.range m, (b ^ 2 ^ (i + 1) + 1)
  have h7 : ∀ m : ℕ, ∑ i ∈ Finset.range m, (1 / ∏ i ∈ Finset.range i, (b ^ 2 ^ (i + 1) + 1) - 1 / ∏ i ∈ Finset.range (i + 1), (b ^ 2 ^ (i + 1) + 1)) = (1 - 1 / ∏ i ∈ Finset.range m, (b ^ 2 ^ (i + 1) + 1)):= by
    intro m
    induction m with
    -- the m = 0 case is proved by simp
    | zero =>
      simp
    -- for the m + 1 case, we use the induction hypothesis and the sum_range_succ theorem
    | succ m ih =>
      simp [Finset.sum_range_succ]
      simp at ih
      linarith
  specialize h7 k
  rw [h5, h6, h7]
  -- show that 1 / ∏ i ∈ Finset.range m, (b ^ 2 ^ (i + 1) + 1) > 0
  have h8 : ∀ i ∈ Finset.range k, b ^ 2 ^ (i + 1) + 1 > 0:= by
    intro i _
    positivity
  replace h8 : ∏ i ∈ Finset.range k, (b ^ 2 ^ (i + 1) + 1) > 0:= by exact Finset.prod_pos h8
  replace h8 : 1 / ∏ i ∈ Finset.range k, (b ^ 2 ^ (i + 1) + 1) > 0:= by exact one_div_pos.2 h8
  replace h8 : 1 - 1 / ∏ i ∈ Finset.range k, (b ^ 2 ^ (i + 1) + 1) < 1:= by linarith
  have h9 : 1 / b > 0:= by exact one_div_pos.2 hbpos
  replace h9 : (1 / b) * (1 - 1 / ∏ i ∈ Finset.range k, (b ^ 2 ^ (i + 1) + 1)) < (1 / b) * 1:= (mul_lt_mul_left h9).mpr h8
  -- simplify the goal to : 1 + (1 / b) = 1 / 2 * (2 + c - √(c ^ 2 - 4))
  suffices 1 + (1 / b) = 1 / 2 * (2 + c - √(c ^ 2 - 4)) by linarith
  replace hc : c ^ 2 > 4:= by nlinarith only [hc]
  -- substitute b = (c + √(c ^ 2 - 4)) / 2 into the goal
  have h10 : 1 / b = (1 / 2) * (c - √(c ^ 2 - 4)):= by
    rw [hb1]
    -- use c > 2 to show √(c ^ 2 - 4) ^ 2 = c ^ 2 - 4
    have hcpos : c + √(c ^ 2 - 4) > 0:= by
      have _ : c > 0:= by
        rw [h1]
        positivity
      positivity
    field_simp
    ring_nf
    rw [show √(-4 + c ^ 2) ^ 2 = -4 + c ^ 2 by refine Real.sq_sqrt (by linarith)]
    linarith
  -- finish the proof by proving 1 + (1 / b) = 1 / 2 * (2 + c - √(c ^ 2 - 4))
  rw [h10]
  linarith
