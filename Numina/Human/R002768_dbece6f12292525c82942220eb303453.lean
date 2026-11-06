import Mathlib

/- Example 7 Let $a_{1}, a_{2}, \cdots, a_{n}$ be positive real numbers. Let

$$

\begin{array}{l}
b_{k}=\frac{a_{1}+a_{2}+\cdots+a_{k}}{k}(k=1,2, \cdots, n), \\
C_{n}=\left(a_{1}-b_{1}\right)^{2}+\left(a_{2}-b_{2}\right)^{2}+\cdots+\left(a_{n}-b_{n}\right)^{2}, \\
D_{n}=\left(a_{1}-b_{n}\right)^{2}+\left(a_{2}-b_{n}\right)^{2}+\cdots+\left(a_{n}-b_{n}\right)^{2} .
\end{array}

$$


Prove: $C_{n} \leqslant D_{n} \leqslant 2 C_{n}$. -/
theorem inequalities_110762 (a b C D : ℕ → ℝ)
  (ha : ∀ i, 0 < a i) (hb : ∀ k, b k = (∑ i ∈ Finset.Icc 1 k, a i) / k)
  (hC : C = fun k => ∑ i ∈ Finset.Icc 1 k, (a i - b i)^2)
  (hD : D = fun k => ∑ i ∈ Finset.Icc 1 k, (a i - b k)^2)
  (k : ℕ)
  : C k ≤ D k ∧ D k ≤ 2 * C k := by

    -- let x_n be 2 * C_n - D_n
    let x : ℕ → ℝ := fun i => 2 * C i - D i

    -- let y_n be D_n - C_n
    let y : ℕ → ℝ := fun i => D i - C i

    -- we have that C_(n+1) - C_n = (a_(k + 1) - b_(k + 1)) ^ 2
    have c_succ_eq : ∀ k, C (k + 1) - C k = (a (k + 1) - b (k + 1)) ^ 2 := by
      intro k
      -- use definition of C
      rw [hC]

      -- combine sums
      rw [←Finset.sum_sdiff_eq_sub (Finset.Icc_subset_Icc (by omega) (by omega))]

      -- but then we only have one term
      have icc_diff : Finset.Icc 1 (k + 1) \ Finset.Icc 1 k = {k+1}
        := Finset.Icc_diff_Ico_self (by omega)

      rw [icc_diff]
      -- simplify
      norm_num

    -- we also have that D_k - D_(k+1)
    -- = - (a (k + 1) - b (k + 1)) ^ 2
    --   - k * (b (k + 1) ^ 2 - (b k) ^ 2)
    --   + 2 * (b (k + 1) - b k) * (∑ i ∈ [1, k], a i)
    have d_succ_eq : ∀ k, D k - D (k + 1)
      = -(a (k + 1) - b (k + 1)) ^ 2
        - k * (b (k + 1) ^ 2 - (b k) ^ 2) + 2 * (b (k + 1) - b k) * (∑ i ∈ Finset.Icc 1 k, a i) := by
      intro k
      -- use definition of D
      rw [hD]

      -- simplify
      norm_num

      -- make sums more similar
      rw [Finset.sum_Icc_succ_top (by omega)]

      -- reorder terms
      convert_to (∑ i ∈ Finset.Icc 1 k, (a i - b k) ^ 2 -
        ∑ k_1 ∈ Finset.Icc 1 k, (a k_1 - b (k + 1)) ^ 2) - (a (k + 1) - b (k + 1)) ^ 2 = _
      · ring

      -- combine sums
      rw [←Finset.sum_sub_distrib]

      -- expand under sum
      have inner_eq : ∀ x, ((a x - b k) ^ 2 - (a x - b (k + 1)) ^ 2)
        = -(a x * b k * 2) + a x * b (1 + k) * 2 + (b k ^ 2 - b (1 + k) ^ 2) := by
          intro x
          ring_nf

      simp_rw [inner_eq]

      -- simplify sums, split and extract constant factors
      norm_num [Finset.sum_add_distrib, ←Finset.sum_mul, ←Finset.mul_sum]

      -- simplify
      ring_nf

    -- and ∑ i ∈ [1, k], a i = b_k * k
    have sum_eq : ∀ k, ∑ i ∈ Finset.Icc 1 k, a i = (b k) * k := by
      intro k
      -- use definition of b
      rw [hb]
      -- consider when k is 0
      by_cases eq_zero : (k : ℝ) = 0
      -- then it's clearly true
      · norm_num at eq_zero
        norm_num [eq_zero]

      -- when k is not 0, we can cancel k and get our equality
      field_simp

    -- x_(k + 1) - x_k is non-negative
    have x_sub_pos : ∀ k : ℕ, 0 ≤ x (k + 1) - x k := by
      intro k
      rw [←ge_iff_le]

      calc x (k + 1) - x k
      _ = (2 * C (k + 1) - D (k + 1)) - (2 * C k - D k) := by rfl
      _ = 2 * (C (k + 1) - C k) + (D k - D (k + 1))  := by ring

      -- use expressions for C_(n+1) - C_n and D k - D (k + 1)
      _ = 2 * (a (k + 1) - b (k + 1)) ^ 2 + (-(a (k + 1) - b (k + 1)) ^ 2
          - k * (b (k + 1) ^ 2 - (b k) ^ 2) + 2 * (b (k + 1) - b k) * (∑ i ∈ Finset.Icc 1 k, a i)) := by rw [c_succ_eq, d_succ_eq]
      -- simplify, rewrite sum
      _ = (a (k + 1) - b (k + 1)) ^ 2 - k * (b (k + 1) ^ 2 - b k ^ 2) + 2 * k * (b k) * (b (k + 1) - b k) := by
          rw [sum_eq]
          ring
      -- rewrite to avoid a values
      _ = ((k + 1) * b (k + 1) - k * b k - b (k + 1)) ^ 2 - k * (b (k + 1) ^ 2 - b k ^ 2) + 2 * k * (b k) * (b (k + 1) - b k) := by
          -- we just changed under the square
          congr
          -- rewrite to just use a values and simplify sums
          rw [hb, hb, Finset.sum_Icc_succ_top (by linarith)]
          -- consider when k is zero
          by_cases k_eq : k = 0
          -- obviously true
          · norm_num [k_eq]

          -- when k is not true we can simplify
          field_simp
      -- group into two factors
      _ = (k ^ 2 - k) * (b (k + 1) - b k) ^ 2 := by ring
      -- which is non-negative
      _ ≥ 0 := by
        -- because the left factor is non-negative
        have left_pos : (0 : ℝ) ≤ (k ^ 2 - k) := by
          simp only [sub_nonneg]
          norm_cast
          refine Nat.le_self_pow ?_ k
          omega
        -- and the right is clearly non-negative, so product is non-negative
        positivity

    -- so x is monotone
    have x_mono : Monotone x := by
      refine monotone_nat_of_le_succ ?_
      intro k
      exact sub_nonneg.mp (x_sub_pos k)

    -- x 0 is zero
    have x_zero : x 0 = 0 := by
      norm_num [x, hC, hD]

    -- y_(k + 1) - y_k is non-negative
    have y_sub_pos : ∀ k : ℕ, 0 ≤ y (k + 1) - y k := by
      intro k

      -- we will simplify the RHS
      rw [←ge_iff_le]
      calc y (k + 1) - y k
      _ = (D (k + 1) - C (k + 1)) - (D k - C k) := rfl
      _ = (D (k + 1) - D k) + (C k - C (k + 1)) := by ring
      _ = -(D k - D (k + 1)) - (C (k + 1) - C k) := by ring
      -- use expressions for C_(n+1) - C_n and D k - D (k + 1)
      _ = -(-(a (k + 1) - b (k + 1)) ^ 2
        - k * (b (k + 1) ^ 2 - (b k) ^ 2) + 2 * (b (k + 1) - b k) * (∑ i ∈ Finset.Icc 1 k, a i)) - ((a (k + 1) - b (k + 1)) ^ 2) := by rw [c_succ_eq, d_succ_eq]
      -- simplify
      _ = k * (b (k + 1) ^ 2 - (b k) ^ 2) - 2 * (b (k + 1) - b k) * (∑ i ∈ Finset.Icc 1 k, a i) := by ring
      -- rewrite sum
      _ = k * (b (k + 1) ^ 2 - (b k) ^ 2) - 2 * (b (k + 1) - b k) * k * b k := by
        rw [sum_eq]
        ring
      -- group into two factors
      _ = k * (b (k + 1) - b k) ^ 2 := by ring
      -- both factors are clearly non-negative, so product is non-negative
      _ ≥ 0 := by positivity

    -- so y is monotone
    have y_mono : Monotone y := by
      refine monotone_nat_of_le_succ ?_
      intro k
      exact sub_nonneg.mp (y_sub_pos k)

    -- y 0 is zero
    have y_zero : y 0 = 0 := by
      norm_num [y, hC, hD]

    split_ands
    -- using that y is always positive we find that C_n ≤ D_n
    · rw [←sub_nonneg, ←y_zero]
      apply y_mono
      omega
    -- using that x is always positive we find that D_n ≤ 2 * C_n
    · rw [←sub_nonneg, ←x_zero]
      apply x_mono
      omega