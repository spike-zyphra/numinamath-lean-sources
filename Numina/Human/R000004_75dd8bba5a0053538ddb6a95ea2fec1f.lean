import Mathlib

/-- Find all solutions of the system of equations in real numbers:

$$
\begin{cases}
x^{3} - x + 1 = y^{2} \\
y^{3} - y + 1 = x^{2}
\end{cases}
$$-/
theorem algebra_4016 (x y : ℝ)
(h1 : x ^ 3 - x + 1 = y ^ 2) (h2 : y ^ 3 - y + 1 = x ^ 2) :
x ^ 2 = 1 ∧ y ^ 2 = 1 := by
  -- Removeing the constant term to the right-hand
  have h1' : x ^ 3 - x = y ^ 2 - 1 := by linarith
  have h2' : y ^ 3 - y = x ^ 2 - 1 := by linarith
  -- Multiply both sides of the `h1'` by $y$.
  have h3 :  y * (x ^ 3 - x) = y * (y ^ 2 - 1) := by
    rw [mul_eq_mul_left_iff.mpr]; left; exact h1'
  nth_rw 2 [mul_sub] at h3; simp at h3
  -- $x * x^2 = x^3$.
  have t : ∀ x : ℝ, x * x ^ 2 = x ^ 3 := by
    intro x
    have t0 : 3 ≠ 0 := by norm_num
    have t1 : 2 = 3 - 1 := by norm_num
    rw [t1]; exact mul_pow_sub_one t0 x
  rw [t y] at h3; rw [h2'] at h3 
  -- replace $y * (y^2 - 1)$ by $x^2 - 1$ because of `h2'`, then square both sides of `h1'`.
  have h3' : (y * (x ^ 3 - x)) ^ 2 = (x ^ 2 - 1) ^ 2 := by
    apply sq_eq_sq_iff_eq_or_eq_neg.mpr; left; exact h3
  rw [mul_pow] at h3'; rw [symm h1] at h3'
  have : x ^ 3 - x = x * (x ^ 2 - 1) := by ring
  nth_rw 2 [this] at h3'; rw [mul_pow] at h3'; rw [← mul_assoc] at h3'
  rw [add_mul] at h3'; rw [sub_mul] at h3'; rw [← pow_add, t x] at h3'
  apply sub_eq_zero.mpr at h3'; nth_rw 2 [← one_mul ((x ^ 2 - 1) ^ 2)] at h3'
  rw [← sub_mul] at h3'; simp at h3'
  -- Discuss two cases $x ^ 5 - x ^ 3 + x ^ 2 - 1 = 0$ or $x ^ 2 - 1 = 0$.
  cases h3' with
  | inl p => rw [← one_mul (x ^ 3)] at p
             have : 5 = 2 + 3 := by norm_num
             rw [this] at p; rw [pow_add] at p; rw [← sub_mul] at p
             rw [← add_sub] at p; nth_rw 2 [← mul_one (x ^ 2 - 1)] at p
             rw [← mul_add] at p; simp at p
             cases p with
             | inl r => rw [r] at h2'
                        nth_rw 2 [← mul_one y] at h2'; rw [← t y] at h2'
                        rw [← mul_sub] at h2'; simp at h2'
                        cases h2' with
                        | inl u => rw [u] at h1
                                   have : x ^ 2 = 1 := by linarith
                                   rw [← t x] at h1; rw [this] at h1; linarith
                        | inr s => constructor
                                   · linarith
                                   · linarith
             | inr s => have : x ^ 3 = -1 := by linarith
                        apply pow_eq_neg_one_iff.mp at this
                        rw [this.left] at h1
                        constructor
                        · rw [this.left]; norm_num
                        · rw [← h1]; norm_num
  | inr q => rw [q] at h2'
             nth_rw 2 [← mul_one y] at h2'; rw [← t y] at h2'
             rw [← mul_sub] at h2'; simp at h2'
             cases h2' with
             | inl r => rw [r] at h1
                        have : x ^ 2 = 1 := by linarith
                        rw [← t x] at h1; rw [this] at h1; linarith
             | inr s => constructor
                        · linarith
                        · linarith
