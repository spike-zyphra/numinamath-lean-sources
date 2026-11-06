import Mathlib

/- Find the mean of all solutions for $x$ when $x^3 + 3x^2 - 10x = 0$. -/
theorem algebra_10561 (r : Set ℝ) (hr : r = setOf (fun (x : ℝ) => x ^ 3 + 3 * x ^ 2 - 10 * x = 0)) :
  (r = {0, 2, -5}) ∧ (∑x ∈ ({0, 2, -5} : Set ℝ), x) / ({0, 2, -5} : Set ℝ).ncard = -1 := by
  constructor
  . -- proof of root of $x ^ 3 + 3 * x ^ 2 - 10 * x = 0$ is ${0, 2, -5}$
    apply Set.ext
    intro x
    constructor
    . -- proof of x ∈ roots → x ∈ {0, -3, 3}
      intro hx
      simp
      rw [hr] at hx; simp at hx
      -- extract x from $x ^ 3 + 3 * x ^ 2 - 10 * x$ we get $x * (x ^ 2 + 3 * x  - 10)$
      rw [show x ^ 3 + 3 * x ^ 2 - 10 * x = x * (x ^ 2 + 3 * x  - 10) by ring_nf] at hx
      rw [mul_eq_zero] at hx
      rcases hx with x_eq_zero | sq_eq_zero
      . -- x = 0
        tauto
      . -- x ^ 2 + 3 * x - 10 = 0
        rw [show x ^ 2 + 3 * x - 10 = 1 * x * x + 3 * x + (-10) by ring_nf] at sq_eq_zero
        rw [mul_assoc, quadratic_eq_zero_iff] at sq_eq_zero
        swap; simp
        swap; exact 7
        ring_nf at sq_eq_zero
        tauto
        rw [discrim]
        linarith
    . -- proof of x ∈ {0, -3, 3} → x ∈ roots
      intro hx
      rw [hr]
      simp; simp at hx
      rcases hx with h1 | h2 | h3
      rw [h1]; linarith
      rw [h2]; linarith
      rw [h3]; linarith
  . -- proof of mean of ${0, 2, -5}$ is $-1$
    have card_eq_3 : ({0, 2, -5} : Set ℝ).ncard = 3 := by
      simp
      have two : 2 ∈ ({2, -5} : Set ℝ) := by simp
      rw [← Set.ncard_diff_singleton_add_one two]
      simp
      exists -5
      simp
      linarith
    rw [card_eq_3]
    simp
    rw [Finset.sum_insert]
    simp
    linarith
    simp
    linarith
