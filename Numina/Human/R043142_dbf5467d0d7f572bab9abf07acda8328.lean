import Mathlib

open Real Set
open scoped BigOperators

/- 10、(20 points) Given $a_{1}, a_{2}, \cdots, a_{n} \in \mathbb{R}^{+}, a=\sum_{i=1}^{n} a_{i}(n \in \mathbb{N}, n \geq 2)$. Find the minimum value of $f\left(a_{1}, a_{2}, \cdots, a_{n}\right)=\sum_{i=1}^{n} \frac{a_{i}}{3 a-a_{i}}$. -/
theorem inequalities_102198 {n : ℕ} (hn : n ≥ 2) :
  IsLeast {x : ℝ |
    ∃ a : ℕ → ℝ, (∀ i ∈ Finset.Ico 0 n, 0 < a i) ∧
      x = ∑ i ∈ Finset.Ico 0 n, a i / (3 * ∑ j ∈ Finset.Ico 0 n, a j - a i)} (n / (3 * n - 1)) := by

  constructor
  · -- the value n / (3n - 1) is obtained when each a i = 1
    let a : ℕ → ℝ := fun _ ↦ 1
    use a
    constructor
    · simp [a]
    field_simp [a]

  -- to show the lower bound, consider the sequence a with
  -- s = ∑ i ∈ Finset.Ico 0 n, a i / (3 * ∑ j ∈ Finset.Ico 0 n, a j - a i)
  intro s ⟨a, a_pos, hs⟩
  -- Let A be the sum ∑ i ∈ Finset.Ico 0 n, a i
  let A := ∑ i ∈ Finset.Ico 0 n, a i
  have h_A : ∑ i ∈ Finset.Ico 0 n, a i = A := by unfold A; rfl

  -- first note that 3 * A - a i > 0 for all i ∈ [0, n-1]
  have h_den_pos : ∀ i ∈ Finset.Ico 0 n, 3 * A - a i > 0 := by
    intro i hi
    have : Finset.Ico 0 n = (Finset.Ico 0 n \ {i}) ∪ {i} := by
      refine Eq.symm (Finset.sdiff_union_of_subset ?_)
      intro i' hi'
      simp at hi'
      rw [hi']
      exact hi
    unfold A
    rw [this]
    rw [Finset.sum_union]
    simp
    rw [mul_add]
    suffices h : ∑ i ∈ (Finset.range n \ {i}), a i ≥ 0 by linarith [a_pos i hi]
    · apply Finset.sum_nonneg
      intro i' hi'
      apply le_of_lt
      apply a_pos i'
      rw [Finset.range_eq_Ico] at hi'
      have := Finset.mem_sdiff.mp hi'
      exact this.1
    exact Finset.sdiff_disjoint

  -- Notice that s = ∑ i ∈ Finset.Ico 0 n, a i / (3 * A - a i)
  --  = ∑ i ∈ Finset.Ico 0 n, (a i + 3 * A - 3 * A) / (3 * A - a i)
  --  = ∑ i ∈ Finset.Ico 0 n, (-1 + 3 * A / (3 * A - a i))
  have h1 : s = ∑ i ∈ Finset.Ico 0 n, (-1 + 3 * A / (3 * A - a i)) := by
    rw [hs]
    apply sub_eq_zero.mp
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro i hi
    rw [sub_eq_zero]
    rw [h_A]
    apply (div_eq_iff ?_).mpr
    rw [add_mul, div_mul_cancel₀]
    ring
    all_goals linarith only [h_den_pos i hi]
  rw [h1]

  -- and ... = -n + ∑ i ∈ Finset.Ico 0 n, 3 * A / (3 * A - a i)
  have h2 : ∑ i ∈ Finset.Ico 0 n, (-1 + 3 * A / (3 * A - a i)) =
    -n + ∑ i ∈ Finset.Ico 0 n, 3 * A / (3 * A - a i) := by
      rw [Finset.sum_add_distrib]
      simp
  rw [h2]

  -- we need the fact that (3 * A - a i) / (3 * A) = 1 - a i / (3 * A) > 0
  have h_one_sub_pos : ∀ i ∈ Finset.Ico 0 n, 1 - a i / (3 * A) > 0 := by
    intro i hi
    have : 3 * A > a i := by linarith only [h_den_pos i hi]
    have : a i / (3 * A) < 1 := by
      refine (div_lt_one ?_).mpr ?_
      suffices h : A > 0 by linarith
      unfold A
      apply Finset.sum_pos
      intro i hi
      exact a_pos i hi
      · simp; linarith only [hn]
      exact this
    linarith only [this]

  -- then ... = ∑ i ∈ Finset.Ico 0 n, (1 - a i / (3 * A))⁻¹
  have h4 : ∑ i ∈ Finset.Ico 0 n, 3 * A / (3 * A - a i) = ∑ i ∈ Finset.Ico 0 n, (1 - a i / (3 * A))⁻¹ := by
    apply sub_eq_zero.mp
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro i hi
    rw [sub_eq_zero]
    field_simp
    apply div_eq_div_iff ?_ ?_ |>.mpr
    rw [mul_sub, mul_div_cancel₀]
    ring
    · suffices h : A > 0 by linarith
      unfold A
      apply Finset.sum_pos
      intro i hi
      exact a_pos i hi
      refine Finset.Aesop.nonempty_Ico_of_lt ?_
      exact Nat.zero_lt_of_lt hn
    linarith only [h_den_pos i hi]
    linarith only [h_one_sub_pos i hi]
  rw [h4]

  -- From Cauchy-Schwartz Inequality we deduce the following result
  have h5 : (∑ i ∈ Finset.Ico 0 n, (1 - a i / (3 * A))) * ∑ i ∈ Finset.Ico 0 n, (1 - a i / (3 * A))⁻¹ ≥ n ^ 2 := by
    have : ∑ i ∈ Finset.Ico 0 n, (1 - a i / (3 * A)) * (1 - a i / (3 * A))⁻¹ = n := by
      have : ∑ i ∈ Finset.Ico 0 n, (1 - a i / (3 * A)) * (1 - a i / (3 * A))⁻¹ = ∑ i ∈ Finset.Ico 0 n, 1 := by
        apply sub_eq_zero.mp
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_eq_zero
        intro i hi
        field_simp
        rw [sub_eq_zero]
        apply div_self
        exact Ne.symm (ne_of_lt (h_one_sub_pos i hi))
      rw [this]
      simp
    rw [← this]
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (Finset.Ico 0 n) ?_ ?_ ?_
    · intro i hi
      exact le_of_lt (h_one_sub_pos i hi)
    · intro i hi
      simp
      apply le_of_sub_nonneg
      exact le_of_lt (h_one_sub_pos i hi)
    intro i hi
    field_simp
    rw [div_self, div_self]
    exact Ne.symm (ne_of_lt (h_one_sub_pos i hi))
    refine pow_ne_zero 2 ?_
    exact Ne.symm (ne_of_lt (h_one_sub_pos i hi))

  -- the above rewrites as the following
  have h6 : (∑ i ∈ Finset.Ico 0 n, (1 - a i / (3 * A))⁻¹) ≥ n ^ 2 / ∑ i ∈ Finset.Ico 0 n, (1 - a i / (3 * A)) := by
    apply div_le_iff₀ ?_ |>.mpr
    rw [mul_comm]
    exact h5
    apply Finset.sum_pos
    intro i hi
    field_simp
    linarith only [h_one_sub_pos i hi]
    refine Finset.Aesop.nonempty_Ico_of_lt ?_
    exact Nat.zero_lt_of_lt hn

  -- so s = ... ≥ -n + n ^ 2 / ∑ i ∈ Finset.Ico 0 n, (1 - a i / (3 * A))
  trans -n + n ^ 2 / ∑ i ∈ Finset.Ico 0 n, (1 - a i / (3 * A))
  swap
  gcongr

  -- now we can calculate
  -- -n + n ^ 2 / ∑ i ∈ Finset.Ico 0 n, (1 - a i / (3 * A)) = -n + n ^ 2 / (n - ∑ i ∈ Finset.Ico 0 n, a i / (3 * A))
  rw [Finset.sum_sub_distrib]
  simp

  -- notice that n - ∑ i ∈ Finset.Ico 0 n, a i / (3 * A) = (3 * A) / (3 * A) = 1/3
  have : ∑ x ∈ Finset.range n, a x / (3 * A) = 1 / 3 := by
    trans A / (3 * A)
    · rw [← Finset.sum_div, Finset.range_eq_Ico]
    field_simp
    rw [mul_comm]
    apply div_self
    suffices h : A > 0 by linarith
    unfold A
    apply Finset.sum_pos
    intro i hi
    exact a_pos i hi
    refine Finset.Aesop.nonempty_Ico_of_lt ?_
    exact Nat.zero_lt_of_lt hn
  rw [this]

  -- on the LHS, we rewrite n + n / (3 * n - 1 : ℝ) = 3 * n ^ 2 / (3 * n - 1)
  have : n + n / (3 * n - 1 : ℝ) = 3 * n ^ 2 / (3 * n - 1) := by
    have : (n : ℝ) = n * (3 * n - 1) / (3 * n - 1) := by
      rw [mul_div_assoc, div_self, mul_one]
      have : (n : ℝ) ≥ 2 := by norm_cast
      linarith only [this]
    nth_rw 1 [this]
    rw [← add_div]

    have : ↑n * (3 * ↑n - 1) + ↑n = (3 * n ^ 2 : ℝ) := by
      ring
    rw [this]
  rw [this]

  -- so we are left to show 3 * n ^ 2 / (3 * n - 1) = n ^ 2 / (n - 1 / 3)
  -- this is routine
  apply le_of_eq
  apply div_eq_div_iff ?_ ?_ |>.mpr
  ring

  linarith only [show (n : ℝ) ≥ 2 by norm_cast]
  linarith only [show (n : ℝ) ≥ 2 by norm_cast]
