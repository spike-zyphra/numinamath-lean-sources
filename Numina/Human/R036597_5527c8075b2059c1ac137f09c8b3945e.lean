import Mathlib

open Finset

/- Some of the $n$ cities are connected by airline routes (all routes are bidirectional). There are exactly $m$ routes. Let $d_i$ be the number of routes departing from city $i$ for $i=1,2, \ldots, n$. If

$$
1 \leq d_i \leq 2010 \quad \text { for every } i=1,2, \ldots, n
$$

prove that

$$
\sum_{i=1}^n d_i^2 \leq 4022 m-2010 n
$$

Determine all $d_i$ for which equality can be achieved.

-/

theorem inequalities_608066 {n : ℕ} (m : ℕ) (d : Fin n → ℤ) (sum_eq : ∑ i, d i = 2 * m)
    (h : ∀ i, 1 ≤ d i ∧ d i ≤ 2010) : ∑ i, (d i)^2 ≤ 4022 * m - 2010 * n
     ∧ (∑ i, (d i)^2 = 4022 * m - 2010 * n ↔ ∀ i, d i ∈ ({1, 2010} : Set ℤ)) := by
  have eq (i): (d i - 1) * (d i - 2010) = (d i) ^ 2 - 2011 * d i + 2010 := by ring
  have iff (i): (d i) ^ 2 = 2011 * d i - 2010 ↔ d i = 1 ∨ d i = 2010 := by
    rw [← Int.sub_eq_zero, ← sub_add, ← eq, mul_eq_zero]
    exact or_congr Int.sub_eq_zero Int.sub_eq_zero
  -- The problem's condition gives us $0 \leq\left(d_i-1\right)\left(2010-d_i\right) \quad \text { for all } i,$
  -- i.e., $d_i^2 \leq 2011 d_i-2010$
  have : ∀ i, (d i) ^ 2 ≤ 2011 * d i - 2010 := by
    intro i
    have : 0 ≥ (d i) ^ 2 - 2011 * d i + 2010 := by
      rw [← eq]
      apply Int.mul_nonpos_of_nonneg_of_nonpos
      repeat linarith[h i]
    linarith[this]
  -- Using the condition, $\sum_{i=1}^n d_i \leq 2011-2010 n$
  have sum_eq' : ∑ i, (2011 * d i - 2010) = 4022 * m - 2010 * n := by
    rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← mul_sum univ d 2011, sum_eq]
    ring
  rw [← sum_eq']
  constructor
  · -- and summing these inequalities, we obtain $\sum_{i=1}^n d_i^2 \leq 2011 \sum_{i=1}^n d_i-2010 n=4022 m-2010 n$
    exact sum_le_sum fun i a => this i
  · set g := fun i ↦ (d i) ^ 2 with hg
    set f := fun i ↦ 2011 * d i - 2010 with hf
    have le : ∀ i, g i ≤ f i := fun i ↦ this i
    -- the inequality holds iff each $d_i^2 = 2011 d_i - 2010$, i.e. $d_i = 1$ or $d_i = 2010$
    have : ∑ i, g i = ∑ i, f i ↔ ∀ i, g i = f i := by
      constructor
      · intro eq
        by_contra nh
        simp at nh
        obtain ⟨i₀, hi⟩ : ∃ i, g i ≠ f i := nh
        have : ∑ i, g i < ∑ i , f i := by
          apply sum_lt_sum (fun i a => this i)
          use i₀
          simpa using (lt_of_le_of_ne (this i₀) hi)
        simp [eq] at this
      · exact fun a => Fintype.sum_congr g f a
    rw [this, hf, hg]
    simpa using forall_congr' iff
