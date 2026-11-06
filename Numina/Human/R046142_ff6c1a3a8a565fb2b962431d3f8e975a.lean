import Mathlib

/- The function $f$ satisfies the functional equation
\[f(x) + f(y) = f(x + y) - xy - 1\]for all real numbers $x$ and $y.$  If $f(1) = 1,$ then find all integers $n$ such that $f(n) = n.$  Enter all such integers, separated by commas. -/
theorem algebra_20733 {f : ℝ → ℝ} (h : ∀ x y, f x + f y = f (x + y) - x * y - 1)
    (h1 : f 1 = 1) :
    {n : ℤ | f n = n} = {1, -2} := by
  -- Setting $x = y = 0,$ we get \[2f(0) = f(0) - 1,\]so $f(0) = -1.$
  have f0eq : f 0 = -1 := by
    have := h 0 0
    simp only [add_zero, mul_zero, sub_zero] at this
    linarith
  -- Setting $y = 1,$ we get \[f(x) + 1 = f(x + 1) - x - 1,\]so \[f(x + 1) - f(x) = x + 2.\]Thus, \[f(n) = \frac{n^2 + 3n - 2}{2}\]for all positive integers $n.$
  have fpos (n : ℕ) : f n = (n ^ 2 + 3 * n - 2) / 2 := by
    induction' n with n hn
    simp only [CharP.cast_eq_zero, f0eq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero, zero_sub, neg_div_self]
    simp only [Nat.cast_add, Nat.cast_one]
    have hneq := h n 1
    rw [hn, h1] at hneq
    linarith
  -- Setting $x = -n$ and $y = n,$ where $n$ is a positive integer, we get \[f(-n) + f(n) = f(0) + n^2 - 1.\]Then the formula \[f(n) = \frac{n^2 + 3n - 2}{2}\]holds for all integers $n.$
  have fneg (n : ℕ) : f (-n) = ((-n) ^ 2 + 3 * (-n) - 2) / 2 := by
    have hneq := h (-n) n
    simp only [neg_add_cancel, neg_mul, sub_neg_eq_add, fpos, f0eq] at hneq
    linarith
  have feq (n : ℤ) : f n = (n ^ 2 + 3 * n - 2) / 2 := by
    if hn : 0 ≤ n then
      have := fpos n.toNat
      have neq : n = n.toNat := by
        exact Eq.symm (Int.toNat_of_nonneg hn)
      rw [neq]
      show f ↑n.toNat = (↑n.toNat ^ 2 + 3 * ↑n.toNat - 2) / 2
      rw [this]
    else 
      have := fneg (-n).toNat
      have neq : n = @Neg.neg ℝ Real.instNeg ↑(-n).toNat := by
        have neq : -n = (-n).toNat := by
          refine Eq.symm (Int.toNat_of_nonneg ?_)
          linarith
        show (n : ℝ) = -↑((-n).toNat : ℤ)
        rw [← neq]
        simp only [Int.cast_neg, neg_neg]
      rw [neq, this]
  -- We want to solve $f(n) = n,$ or \[\frac{n^2 + 3n - 2}{2} = n.\]Then $n^2 + 3n - 2 = 2n,$ or $n^2 + n - 2 = 0.$  This factors as $(n - 1)(n + 2) = 0,$ so the solutions are $n = \boxed{1,-2}.$
  ext x
  constructor
  intro hx
  simp only [feq, Set.mem_setOf_eq] at hx
  apply sub_eq_zero_of_eq at hx
  have eq : (↑x ^ 2 + 3 * ↑x - 2 : ℝ) / 2 - ↑x = (x - 1) * (x + 2) * 2⁻¹ := by
    ring
  rw [eq] at hx
  simp only [mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, or_false] at hx
  rcases hx with hx | hx
  have xeq : (x : ℝ) = (1 : ℤ) := by
    simp only [Int.cast_one]
    linarith
  left
  exact Int.cast_injective xeq
  right
  simp only [Int.reduceNeg, Set.mem_singleton_iff]
  have xeq : (x : ℝ) = (-2 : ℤ) := by
    simp only [Int.reduceNeg, Int.cast_neg, Int.cast_ofNat]
    linarith
  exact Int.cast_injective xeq
  intro xin
  rcases xin with xeq | xeq
  simp only [feq, xeq, Set.mem_setOf_eq, Int.cast_one, one_pow, mul_one]
  norm_num
  rw [Set.mem_singleton_iff] at xeq
  simp only [feq, xeq, Int.reduceNeg, Set.mem_setOf_eq, Int.cast_neg, Int.cast_ofNat, even_two, Even.neg_pow, mul_neg]
  norm_num
  