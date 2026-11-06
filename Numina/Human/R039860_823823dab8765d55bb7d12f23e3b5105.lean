import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Data.Real.Sqrt

open Real

/- Example 3 Suppose there is a sequence of positive real numbers $\left\{a_{n}\right\}$ such that the expression $\frac{a_{k}+a_{n}}{1+a_{k} \cdot a_{n}}$ depends only on the sum of the indices $k+n$, that is, when $k+n=m+l$, it must be that $\frac{a_{k}+a_{n}}{1+a_{k} \cdot a_{n}}=\frac{a_{m}+a_{l}}{1+a_{m} \cdot a_{l}}$. Prove: The sequence $\left\{a_{n}\right\}$ is bounded. -/
theorem algebra_290824 (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (h : ∀ k n m l, k + n = m + l → (a k + a n) / (1 + a k * a n) =
      (a m + a l) / (1 + a m * a l)) :
    ∃ B, ∀ n, |a n| ≤ B := by
  let α := min (a 0) (1 / a 0)
  let m := (1 - sqrt (1 - α^2)) / α
  let M := (1 + sqrt (1 - α^2)) / α
  -- Show that α is positive
  have α_pos : 0 < α := by
    apply lt_min
    · exact ha 0
    simp [ha 0]
  -- Show that m ≤ M
  have m_le_M : m ≤ M := by
    unfold m M
    rw [div_le_div_iff_of_pos_right α_pos]
    apply add_le_add_left
    simp
  -- Show that m ≤ a n ≤ M for all n
  have bounds : ∀ n, m ≤ a n ∧ a n ≤ M := by
    let A n := (a 0 + a n) / (1 + a 0 * a n)
    -- Use the condition of the problem
    have A_sum_ind (N k l : ℕ) : N = k + l → A N = (a k + a l) / (1 + a k * a l) := by
      intro hN
      unfold A
      exact h 0 N k l (show 0 + N = k + l by linarith)
    -- Show that A n ≥ α
    have alpha_bound : ∀ n, α ≤ A n := by
      intro n
      -- A positivity result
      have denom_pos : 0 < 1 + a 0 * a n := by linarith [mul_pos (ha 0) (ha n)]
      -- Do case work on whether α ≤ 1 or 1 ≤ α
      rcases LinearOrder.le_total (a 0) 1 with small | big
      -- Value of α in this case is a 0
      · have α_val : α = a 0 := by
          apply min_eq_left
          rw [le_div_iff₀ (ha 0), ← one_mul 1]
          apply mul_le_mul small small <;> linarith [ha 0]
        rw [α_val, le_div_iff₀ denom_pos]
        simp [mul_add]
        calc
          a 0 * (a 0 * a n) ≤ a 0 * a n := mul_le_of_le_one_left (mul_nonneg (by linarith [ha 0]) (by linarith [ha n])) (small)
          _ ≤ a n := mul_le_of_le_one_left (by linarith [ha n]) (small)
      -- Value of α in this case is 1 / a 0
      have α_val : α = 1 / a 0 := by
        apply min_eq_right
        rw [div_le_iff₀ (ha 0)]
        nlinarith
      rw [α_val, le_div_iff₀ denom_pos, mul_add, mul_one, ← mul_assoc, div_mul_cancel₀ 1 (by linarith [ha 0]), one_mul]
      apply add_le_add_right
      rw [div_le_iff₀ (ha 0)]
      nlinarith
    intro n
    -- Specialize to A (n + n)
    have : α ≤ 2 * a n / (1 + (a n)^2) := by
      rw [two_mul, pow_two, ← A_sum_ind (n + n) n n (by rfl)]
      exact alpha_bound (n + n)
    -- Obtain a quadratic inequality for a n
    have quadratic_bound : α * (a n)^2 - 2 * a n + α ≤ 0 := by
      have : α ≤ 2 * a n / (1 + a n ^ 2) := this
      -- Prove that the denominator is positivie
      have denom_pos : 0 < 1 + a n ^ 2 := by
        calc
          1 + a n ^ 2 ≥ 1 + 0 := by nlinarith
          _ > 0 := by norm_num
      rw [le_div_iff₀ denom_pos] at this
      linarith
    -- Use the fact that m and M are roots of the quadratic to factor it
    have factor_quadratic : α * (a n)^2 - 2 * a n + α = α * (a n - m) * (a n - M) := by
      -- Inequality for positivity
      have : 0 ≤ 1 - α ^ 2 := by
        simp
        rw [abs_eq_self.mpr (by linarith), min_le_iff, one_div_le (ha 0) zero_lt_one, one_div_one]
        exact LinearOrder.le_total (a 0) 1
      unfold m M
      field_simp
      -- Use difference of squares and positivity to expand
      rw [← sub_sub, ← sub_add, ← sq_sub_sq, sq_sqrt this]
      ring
    rw [factor_quadratic] at quadratic_bound
    -- Prove the inequalities
    -- Use the contrapositive
    contrapose quadratic_bound
    rw [not_and_or] at quadratic_bound
    push_neg at quadratic_bound
    push_neg
    rcases quadratic_bound with small | big
    -- Case 1 : a n < m
    · have f1 : a n - M < 0 := by linarith
      have f2 : a n - m < 0 := by linarith
      rw [mul_assoc, mul_pos_iff]
      left
      refine ⟨α_pos, ?_⟩
      exact mul_pos_of_neg_of_neg f2 f1
    -- Case 2 : a n > M
    have f1 : a n - m > 0 := by linarith
    have f2 : a n - M > 0 := by linarith
    rw [mul_assoc, mul_pos_iff]
    left
    refine ⟨α_pos, ?_⟩
    exact mul_pos f1 f2
  -- Use max(|m|, |M|) as our B
  use max |m| |M|
  intro n
  apply abs_le.mpr
  constructor
  -- Prove lower bound
  · calc
      - max |m| |M| = min (-|m|) (-|M|) := by rw [← min_neg_neg]
      _ ≤ -|m| := by simp
      _ ≤ m := neg_abs_le m
      _ ≤ a n := (bounds n).1
  -- Prove upper bound
  calc
    a n ≤ M := (bounds n).2
    _ ≤ |M| := le_abs_self M
    _ ≤ max |m| |M| := by simp