import Mathlib

/- 9.1. Given quadratic trinomials $f_{1}(x)=x^{2}+2 a_{1} x+b_{1}, f_{2}(x)=$ $=x^{2}+2 a_{2} x+b_{2}, f_{3}(x)=x^{2}+2 a_{3} x+b_{3}$. It is known that $a_{1} a_{2} a_{3}=$ $=b_{1} b_{2} b_{3}>1$. Prove that at least one of these trinomials has two roots.

(N. Agakhanov) -/
theorem algebra_105745 {a b : Fin 3 → ℝ} (h : ∏ i, a i = ∏ i, b i) (h1 : ∏ i, b i > 1) :
    ∃ i, ∃ x1 x2, x1 ≠ x2 ∧ x1^2 + 2 * a i * x1 + b i = 0 ∧ x2^2 + 2 * a i * x2 + b i = 0 := by
  -- Assume that there is no equation with 2 distinct roots and show that ∏ i, b i ≤ 1.
  contrapose! h1
  -- It is enought to show that a i ^ 2 ≤ b i for all i.
  suffices hab : ∀ i, a i ^ 2 ≤ b i by
    -- Define p = ∏ i, a i.
    set p := ∏ i, a i
    -- Show that p^2 ≤ p.
    have hp : p ^ 2 ≤ p := calc
      -- We have p^2 = ∏ i, a i ^ 2 ≤ ∏ i, b i (from the assumption a i ^ 2 ≤ b i)
      --             = p.
      p ^ 2 = ∏ i, a i ^ 2 := by rw [Finset.prod_pow]
      _ ≤ ∏ i, b i := by
        apply Finset.prod_le_prod
        · intro i hi
          positivity
        · intro i hi
          exact hab i
      _ = p := by rw [h]
    -- p^2 ≤ p is equivalent to 0 ≤ p * (1 - p).
    replace hp : 0 ≤ p * (1 - p) := by linear_combination hp
    rw [mul_nonneg_iff] at hp
    -- We conclude that p ≤ 1.
    cases' hp with hp hp <;> linarith
  -- Assume now that there exists i such that a i ^ 2 > b i and show that there is
  -- an equation with 2 distinct roots.
  contrapose! h1
  have ⟨i, hi⟩ := h1
  use i
  -- The discriminant of the i-th equation is positive and so it is a square of some number s.
  have ⟨s, hs, hs0⟩ : ∃ s, discrim 1 (2 * a i) (b i) = s * s ∧ 0 < s := by
    use √(discrim 1 (2 * a i) (b i))
    constructor
    · rw [← pow_two, Real.sq_sqrt]
      simp [discrim, mul_pow]
      linarith
    · apply Real.sqrt_pos_of_pos
      simp [discrim, mul_pow]
      linarith
  -- Show that x1 = (-2 * a i + s) / 2 and x2 = (-2 * a i - s) / 2 are roots
  -- of the i-th equation and x1 ≠ x2.
  use (-(2 * a i) + s) / 2, (-(2 * a i) - s) / 2
  have heq := quadratic_eq_zero_iff (by norm_num) hs
  constructorm* _ ∧ _
  · linarith
  · have := heq ((-(2 * a i) + s) / 2)
    simp at this
    linear_combination this
  · have := heq ((-(2 * a i) - s) / 2)
    simp at this
    linear_combination this