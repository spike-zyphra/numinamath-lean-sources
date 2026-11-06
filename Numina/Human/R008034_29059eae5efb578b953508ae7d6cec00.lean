import Mathlib

/- Solve for $n$: $\frac{2-n}{n+1} + \frac{2n-4}{2-n} = 1$. -/
theorem algebra_10421 {n : ℝ} (hn : n ≠ -1 ∧ n ≠ 2) : (2 - n) / (n + 1) + (2 * n - 4) / (2 - n) = 1 ↔ n = -1 / 4 := by
  -- note that (2n-4)/(2-n) = -2
  have h1: (2*n-4)/(2-n) = -2 := by
    have: 2-n ≠ 0 := by
      by_contra! hc
      have: n = 2 := by
        rw [← add_zero n, ← hc]; simp
      rw [this] at hn
      have := hn.right
      norm_num at this
    field_simp [this]; ring
  -- substitute (2n-4)/(2-n) =-2, the original equation turns to be (2-n)/(n+1) = 3
  have h2: (2-n)/(n+1)+(2*n-4)/(2-n) = 1 ↔ (2-n)/(n+1) = 3 := by
    rw [h1]
    have: (3:ℝ) = 1 + 2 := by norm_num
    rw [this]
    exact add_neg_eq_iff_eq_add
  -- multiply n+1 to both sides, and we get 2-n = 3n+3
  have h3: (2-n)/(n+1) = 3 ↔ 2-n = 3*n+3 := by
    have ht1: n+1 ≠ 0 := by
      by_contra! hc
      have ht1: n = -1 := by
        rw [← add_zero (-1), ← hc]; ring
      have := hn.left
      rw [ht1] at this; norm_num at this
    have: 3*n+3 = 3*(n+1) := by ring
    rw [this]
    exact div_eq_iff ht1
  -- 2-n=3n+3, therefore 4n=-1
  have h4: 2-n=3*n+3 ↔ n*4 = -1 := by
    have ht1: n*4 = (3*n+3) + n - 3 := by ring
    constructor <;> intro h
    rw [← h] at ht1; rw [ht1]; ring
    rw [ht1] at h
    have ht2: 3*n+3 = 3*n+3+n-3 -(n-3) := by ring
    rw [ht2, h]; ring
  rw [h2, h3, h4]
  -- 4n=-1, so n=-1/4
  have: (4:ℝ) ≠ 0 := by norm_num
  exact Iff.symm (eq_div_iff this)