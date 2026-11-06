import Mathlib

open Finset Real

/- Example 7 Let $a_{1}, a_{2}, \cdots, a_{n}$ be positive real numbers. Let
$$
\begin{array}{l}
b_{k}=\frac{a_{1}+a_{2}+\cdots+a_{k}}{k}(k=1,2, \cdots, n), \\
C_{n}=\left(a_{1}-b_{1}\right)^{2}+\left(a_{2}-b_{2}\right)^{2}+\cdots+\left(a_{n}-b_{n}\right)^{2}, \\
D_{n}=\left(a_{1}-b_{n}\right)^{2}+\left(a_{2}-b_{n}\right)^{2}+\cdots+\left(a_{n}-b_{n}\right)^{2} .
\end{array}
$$

Prove: $C_{n} \leqslant D_{n} \leqslant 2 C_{n}$. -/
theorem inequalities_110762 {n : ℕ} (hn : 0 < n) (a b : ℕ → ℝ)
    (ha : ∀ i ∈ Icc 1 n, 0 < a i) (hb : ∀ k ∈ Icc 1 n, b k = (∑ i in Icc 1 k, a i) / k)
    (C D : ℝ) (hC : C = ∑ i ∈ Icc 1 n, (a i - b i)^2)
    (hD : D = ∑ i ∈ Icc 1 n, (a i - b n)^2) :
    C ≤ D ∧ D ≤ 2 * C := by

    -- we need the connection between a i and b i, that is:
    -- a (i + 1) = (i + 1) * (b (i + 1)) - i * b i
    have ha_i (i : ℕ) (hi : i ∈ Icc 1 n) (hi' : i + 1 ∈ Icc 1 n) :
      a (i + 1) = (i + 1) * (b (i + 1)) - i * b i := by
        rw [hb i hi, hb (i + 1) hi']  -- unfold the definition of b_i and b_{i+1}
        have : (i : ℝ) > 0 := by simp_all; linarith
        field_simp  -- cancel *k and /k
        rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 i)]
        ring

    -- First, we define sequences C' and D' similar to C_n and D_n
    let C' : ℕ → ℝ := fun k ↦ ∑ i ∈ Icc 1 k, (a i - b i)^2
    let D' : ℕ → ℝ := fun k ↦ ∑ i ∈ Icc 1 k, (a i - b k)^2

    -- so that we have C n = C, and D n = D
    have hCn : C = C' n := by simp [C', hC]
    have hDn : D = D' n := by simp [D', hD]

    -- Let X n := 2 * C' n - D' n, Y n := D' n - C' n be the differences
    let X : ℕ → ℝ := fun k ↦ 2 * C' k - D' k
    let Y : ℕ → ℝ := fun k ↦ D' k - C' k

    -- We only need to prove that X n ≥ 0 and Y n ≥ 0
    suffices h : X n ≥ 0 ∧ Y n ≥ 0 by
      unfold X at h
      unfold Y at h
      obtain ⟨hXn, hYn⟩ := h
      rw [hCn, hDn]
      constructor <;> linarith

    constructor
    · -- Part 1 : show that X n ≥ 0
      -- 1. we prove that X n is a monotone increasing sequence
      have hX_mono : MonotoneOn X (Icc 1 n) := by
        -- unfold the definitions of each sequences
        unfold X; unfold C'; unfold D'
        -- we prove by show that X (k + 1) ≥ X k
        apply monotoneOn_of_le_add_one
        simp
        · exact Set.ordConnected_Icc
        rintro k _ kmem k'mem
        -- which is equivalent to prove X (k + 1) - X k ≥ 0
        apply le_of_sub_nonneg
        -- split the last summand in ∑ i ∈ [1, k + 1]
        rw [Finset.sum_Icc_succ_top, Finset.sum_Icc_succ_top]
        generalize ∑ i ∈ Icc 1 k, (a i - b i) ^ 2 = t
        -- then we do a boring calculation, most steps stands for themselves and are trivial
        calc
          2 * (t + (a (k + 1) - b (k + 1)) ^ 2) -
            (∑ k_1 ∈ Icc 1 k, (a k_1 - b (k + 1)) ^ 2 + (a (k + 1) - b (k + 1)) ^ 2) -
            (2 * t - ∑ i ∈ Icc 1 k, (a i - b k) ^ 2)
            = ((a (k + 1) - b (k + 1)) ^ 2) -
              (∑ i ∈ Icc 1 k, (a i - b (k + 1)) ^ 2 - ∑ i ∈ Icc 1 k, (a i - b k) ^ 2) := by ring
          _ = ((a (k + 1) - b (k + 1)) ^ 2) - (∑ i ∈ Icc 1 k, ((a i - b (k + 1)) ^ 2 - (a i - b k) ^ 2)) := by
                rw [Finset.sum_sub_distrib]
          _ = ((a (k + 1) - b (k + 1)) ^ 2) -
                (∑ i ∈ Icc 1 k, (b (k + 1) ^ 2 - b k ^ 2 - 2 * (b (k + 1) - b k) * a i)) := by congr; ext i; ring
          _ = ((a (k + 1) - b (k + 1)) ^ 2) -
                ((∑ i ∈ Icc 1 k, (b (k + 1) ^ 2 - b k ^ 2)) - ∑ i ∈ Icc 1 k, 2 * (b (k + 1) - b k) * a i) := by
                rw [← Finset.sum_sub_distrib]
          _ = ((a (k + 1) - b (k + 1)) ^ 2) -
                (k * (b (k + 1) ^ 2 - b k ^ 2) - ∑ i ∈ Icc 1 k, 2 * (b (k + 1) - b k) * a i) := by
                congr
                rw [Finset.sum_eq_card_nsmul (b := (b (k + 1) ^ 2 - b k ^ 2))]
                simp; intros; rfl
          _ = ((a (k + 1) - b (k + 1)) ^ 2) -
                (k * (b (k + 1) ^ 2 - b k ^ 2) - 2 * (b (k + 1) - b k) * ∑ i ∈ Icc 1 k, a i) := by
                congr
                exact Eq.symm (mul_sum (Icc 1 k) a (2 * (b (k + 1) - b k)))
          _ = ((a (k + 1) - b (k + 1)) ^ 2) - k * (b (k + 1) ^ 2 - b k ^ 2) +
              2 * (b (k + 1) - b k) * ∑ i ∈ Icc 1 k, a i := by ring
          _ = ((a (k + 1) - b (k + 1)) ^ 2) - k * (b (k + 1) ^ 2 - b k ^ 2) +
              2 * (b (k + 1) - b k) * (k * b k) := by
              congr
              -- for this step, we need the fact that ∑ i ∈ Icc 1 k, a i = k * b k
              -- this is proved by expanding the definition of b and cancel the denominator
              rw [hb k kmem]
              have : (k : ℝ) > 0 := by simp; simp at kmem; linarith
              field_simp
          _ = ((a (k + 1) - b (k + 1)) ^ 2) - k * (b (k + 1) - b k) ^ 2 := by ring
          _ = (k * (b (k + 1) - b k)) ^ 2 - k * (b (k + 1) - b k) ^ 2 := by
              congr
              -- for this step, we need the fact a (k + 1) = (k + 1) * (b (k + 1)) - k * b k
              -- which has been proved in the very beginning
              have := ha_i k (show k ∈ Icc 1 n by simp_all) (show (k + 1) ∈ Icc 1 n by simp_all)
              rw [this]; ring
          _ = (k ^ 2 - k) * (b (k + 1) - b k) ^ 2 := by ring
          _ ≥ 0 := by
              apply mul_nonneg
              simp
              · norm_cast
                exact Nat.le_self_pow (show 2 ≠ 0 by norm_num) k
              exact sq_nonneg (b (k + 1) - b k)
        all_goals exact Nat.le_add_left 1 k

      -- 2. we prove the first item X 1 ≥ 0
      have hX1 : X 1 ≥ 0 := by
        unfold X; unfold C'; unfold D'
        simp
        linarith [sq_nonneg (a 1 - b 1)]

      -- 3. by monotonicity, we show X n ≥ X 1 ≥ 0, finishing the proof
      suffices h : X n ≥ X 1 by linarith
      apply hX_mono
      repeat simp; linarith
      linarith

    · -- Part 2 : show that Y n ≥ 0
      -- 1. we prove that Y n is a monotone increasing sequence
      have hY_mono : MonotoneOn Y (Icc 1 n) := by
        -- unfold the definitions of each sequences
        unfold Y; unfold C'; unfold D'
        -- we prove by show that Y (k + 1) ≥ Y k
        apply monotoneOn_of_le_add_one
        simp
        · exact Set.ordConnected_Icc
        rintro k hk kmem k'mem
        -- which is equivalent to prove Y (k + 1) - Y k ≥ 0
        apply le_of_sub_nonneg
        -- split the last summand in ∑ i ∈ [1, k + 1]
        rw [Finset.sum_Icc_succ_top, Finset.sum_Icc_succ_top]
        simp
        apply le_of_sub_nonneg
        -- then we do a boring calculation, most steps stands for themselves and are trivial
        rw [← Finset.sum_sub_distrib]
        calc
          ∑ x ∈ Icc 1 k, ((a x - b (k + 1)) ^ 2 - (a x - b k) ^ 2)
            = ∑ i ∈ Icc 1 k, ((b (k + 1) ^ 2 - b k ^ 2) - 2 * (b (k + 1) - b k) * a i) := by
              congr; ext i; ring
          _ = (∑ i ∈ Icc 1 k, (b (k + 1) ^ 2 - b k ^ 2)) - (∑ i ∈ Icc 1 k, 2 * (b (k + 1) - b k) * a i) := by
              rw [Finset.sum_sub_distrib]
          _ = k * (b (k + 1) ^ 2 - b k ^ 2) - (∑ i ∈ Icc 1 k, 2 * (b (k + 1) - b k) * a i) := by
              congr
              rw [Finset.sum_eq_card_nsmul (b := (b (k + 1) ^ 2 - b k ^ 2))]
              simp; intros; rfl
          _ = k * (b (k + 1) ^ 2 - b k ^ 2) - 2 * (b (k + 1) - b k) * (∑ i ∈ Icc 1 k, a i) := by
              congr
              exact Eq.symm (mul_sum (Icc 1 k) a (2 * (b (k + 1) - b k)))
          _ = k * (b (k + 1) ^ 2 - b k ^ 2) - 2 * (b (k + 1) - b k) * (k * b k) := by
              congr
              -- for this step, we need the fact that ∑ i ∈ Icc 1 k, a i = k * b k
              -- this is proved by expanding the definition of b and cancel the denominator
              rw [hb k kmem]
              have : (k : ℝ) > 0 := by simp; simp at kmem; linarith
              field_simp
          _ = k * (b (k + 1) - b k) ^ 2 := by ring
          _ ≥ 0 := by
              apply mul_nonneg;
              norm_cast; exact Nat.zero_le k
              exact sq_nonneg (b (k + 1) - b k)
        all_goals exact Nat.le_add_left 1 k

      -- 2. we prove the first item Y 1 ≥ 0
      have hY1 : Y 1 ≥ 0 := by unfold Y; unfold C'; unfold D'; simp

      -- 3. by monotonicity, we show Y n ≥ Y 1 ≥ 0, finishing the proof
      suffices h : Y n ≥ Y 1 by linarith
      apply hY_mono
      repeat simp; linarith
      linarith
