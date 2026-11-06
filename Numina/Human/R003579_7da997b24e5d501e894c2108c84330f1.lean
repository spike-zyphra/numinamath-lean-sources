import Mathlib

open Real Set
open scoped BigOperators

/- Prove that for any positive integer $n$, if $\alpha=\frac{180^{\circ}}{1+2^{n}}$, then


$$

(\cos \alpha) \cdot(\cos 2 \alpha) \cdot(\cos 4 \alpha) \cdots \cdots\left(\cos 2^{n-1} \alpha\right)=\frac{1}{2^{n}}

$$
 -/
theorem algebra_198122 (n : ℕ) (hn : 0 < n) (α : ℝ)
  (hα : α = π / (1 + 2 ^ n)) :
  ∏ k ∈ Finset.range n, cos (2 ^ k * α) = 1 / 2 ^ n := by
  -- let's multiply both sides, each term on the left by 2, rhs by 2^n
  suffices ∏ k ∈ Finset.range n, 2 * cos (2 ^ k * α) = 1 by
    rw [Finset.prod_mul_distrib, Finset.prod_const] at this
    simp at this
    apply congr_arg (fun t => t / 2 ^ n) at this
    rw [← this, mul_comm, mul_div_assoc, div_self (by simp), mul_one]
  -- now we multiply both sides by sin α
  -- first we show sin α ≠ 0
  have hα' : sin α ≠ 0 := by
    refine sin_ne_zero_iff.mpr ?_
    intro m hm
    rw [← hm] at hα
    have h2:↑0 = π * m - π/ (1 + 2 ^ n) := by
      linarith
    rw [show π * (m:ℝ) - π / (1 + 2 ^ n)=π*(m-1/(1+2^n)) by ring_nf] at h2
    apply zero_eq_mul.mp at h2
    cases' h2 with h2l h2r
    · apply pi_ne_zero; assumption
    · apply congr_arg (fun t => t * (1 + 2 ^ n)) at h2r
      rw [zero_mul, sub_mul, div_mul, div_self (by apply ne_of_gt; positivity), div_one] at h2r
      cases' lt_trichotomy m 0 with hm0 hm1
      · suffices (m:ℝ) * (1 + 2 ^ n) - 1 < 0 by linarith
        rw [sub_eq_add_neg]
        apply add_neg
        rotate_left; norm_num
        apply mul_neg_of_neg_of_pos
        norm_cast
        positivity
      cases' hm1 with hm1l hm1r
      · rw [hm1l] at h2r
        simp at h2r
      suffices (m:ℝ) * (1 + 2 ^ n) - 1 > 0 by linarith
      let q:∃ m':ℕ, m' = m := by
        use Int.toNat m
        simp; linarith
      obtain ⟨m', m'def⟩ := q
      rw [← m'def]
      simp
      norm_cast
      refine Nat.one_lt_mul_iff.mpr ?_
      constructor
      linarith
      constructor
      positivity
      right
      simp
  suffices sin α * ∏ k ∈ Finset.range n, 2 * cos (2 ^ k * α) = sin α by
    apply congr_arg (fun t => t * (sin α)⁻¹) at this
    rw [mul_inv_cancel₀ (by assumption), mul_comm (sin α), mul_assoc, mul_inv_cancel₀ (by assumption), mul_one] at this
    exact this
  -- we can telescope the left product
  have h3:∀ α':ℝ,∀ n':ℕ, sin α' * ∏ k ∈ Finset.range n', 2 * cos (2 ^ k * α') = sin (2 ^ n' * α') := by
    intro α' n'
    induction n' with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ, ← mul_assoc, ih, ← mul_assoc, mul_comm (sin _), Real.two_mul_sin_mul_cos, sub_self, sin_zero, zero_add]
      ring_nf
  specialize h3 α n; rw [h3]
  -- now let's multiply hα by denominator to obtain 2^nα in a simpler way
  apply congr_arg (fun t => t * (1 + 2 ^ n)) at hα
  rw [div_mul, div_self (by apply ne_of_gt; positivity), div_one, mul_add, mul_one, mul_comm] at hα
  have h4: 2^n * α = π - α := by linarith
  rw [h4]
  exact sin_pi_sub α