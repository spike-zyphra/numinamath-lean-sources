import Mathlib

/- Find all pairs $(a, b)$ of positive integers such that

$$
11 a b \leq a^{3}-b^{3} \leq 12 a b
$$

Answer:  $(a, b)=(5,2)$.-/
theorem inequalities_605334 (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    11 * a * b ≤ a ^ 3 - b ^ 3 ∧ a ^ 3 - b ^ 3 ≤ 12 * a * b ↔ (a, b) = (5, 2) := by
  constructor
  · rintro ⟨h1, h2⟩

    -- First, from $a^{3}-b^{3} \geq 11 a b > 0$ it follows that $a > b$, implying that $a-b \geq 1$.
    have hblta : b < a := by
      have : a ^ 3 > b ^ 3 := calc
        _ = (a ^ 3 - b ^ 3) + b ^ 3 := by
          omega
        _ ≥ 11 * a * b + b ^ 3 := by
          exact (Int.add_le_add_iff_right (b ^ 3)).mpr h1
        _ > b ^ 3 := by
          linarith [Int.mul_pos ha hb]
      rw [pow_three, pow_three] at this
      nlinarith

    -- we show that $a-b < 4$ so $a-b \in {1,2,3}$.
    have hub : a - b < 4 := by
      -- \begin{aligned}
      -- a^{3}-b^{3} &= (a-b)\left(a^{2}+a b+b^{2}\right)\\
      -- &= (a-b)\left[(a-b)^{2}+3 a b\right] \\
      -- &\geq (a-b)(1+3 a b) \\
      -- &> 3 a b(a-b)
      -- \end{aligned}
      -- $$
      have : a ^ 3 - b ^ 3 > (a - b) * 3 * a * b := calc
        _ = (a - b) * (a ^ 2 + a * b + b ^ 2) := by
          linarith
        _ = (a - b) * ((a - b) ^ 2 + 3 * a * b) := by
          linarith
        _ ≥ (a - b) * (1 + 3 * a * b) := by
          gcongr
          · omega
          · nlinarith
        _ > (a - b) * 3 * a * b := by
          linarith
      -- Therefore $12 a b \geq a^{3}-b^{3} > 3 a b(a-b)$, which implies that $a-b < 4$.
      have : 3 * a * b * (a - b) < 12 * a * b := calc
        _ < a ^ 3 - b ^ 3 := by linarith
        _ ≤ 12 * a * b := h2
      rw [show (12 : ℤ) * a * b = 3 * a * b * 4 by linarith] at this
      apply lt_of_mul_lt_mul_of_nonneg_left at this
      apply this
      linarith

    -- We discuss three possible cases:
    rcases (by omega : a - b = 1 ∨ a - b = 2 ∨ a - b = 3) with hc1 | hc2 | hc3
    -- After replacing $a=b+1$, the condition $a^{3}-b^{3} \geq 11 a b$ reduces to $1 \geq 8 b^{2}+8 b$, which is not satisfied for any positive integer $b$.
    · exfalso
      have ub : b ^ 2 * 8 + b * 8 ≤ 1 := by
        rw [show a = b + 1 by omega, pow_three, ← sub_nonneg] at h1
        ring_nf at h1
        rw [← sub_neg_eq_add, sub_nonneg, neg_sub, sub_neg_eq_add] at h1
        exact h1
      have lb : 16 ≤ b ^ 2 * 8 + b * 8 := by
        calc
          _ ≤ 8 + 8 := by omega
          _ ≤ 8 + b * 8 := by omega
          _ ≤ b ^ 2 * 8 + b * 8 := by nlinarith
      linarith

    -- After replacing $a=b+2$, the condition $a^{3}-b^{3} \geq 11 a b$ reduces to $8 \geq 5 b^{2}+10 b$, which is also not satisfied for any positive integer $b$.
    · exfalso
      rw [show a = b + 2 by omega] at h1
      replace h1 := sub_nonneg_of_le h1
      ring_nf at h1
      have := by calc
        (15 : ℤ) = 5 + 10 := by
          omega
        _ ≤ 5 + 10 * b := by linarith
        _ ≤ 5 * b * b + 10 * b := by nlinarith
        _ ≤ 8 := by linarith
      exact (Int.negSucc_not_nonneg 6).mp this

    -- After replacing $a=b+3$, the condition $a^{3}-b^{3} \geq 11 a b$ reduces to $27 \geq 2 b^{2}+6 b$.
    -- This holds true only for $b=1$ and $b=2$.
    · rw [show a = b + 3 by omega] at h1
      have : b = 1 ∨ b = 2 := by
        suffices h : b < 3 by omega
        replace h1 := sub_nonneg_of_le h1
        ring_nf at h1
        by_contra hb'
        push_neg at hb'
        have := calc
          (36 : ℤ) = 6 * 3 + 2 * 3 ^ 2 := by
            decide
          _ ≤ 6 * b + 2 * 3 ^ 2 := by
            omega
          _ ≤ 6 * b + 2 * b ^ 2 := by
            nlinarith
          _ ≤ 27 := by
            linarith
        norm_num at this

      rcases this with h | h
      -- For $b=1$ we get $a=4$ but this contradicts the upper bound for $a^3 - b^3$.
      · have : a = 4 := by omega
        rw [h, this] at h2
        norm_num at h2
      -- For $b=2$ we get $a=5$.
      · rw [Prod.mk.injEq]
        exact ⟨show a = 5 by omega, h⟩

  -- It is easy to check that $(5, 2)$ solves the required inequality.
  · rintro ⟨_ ,_⟩
    constructor <;> simp [hb, ha]
