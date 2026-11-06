import Mathlib

theorem Complex.ne_zero_of_re_pos : ∀ {s : ℂ}, 0 < s.re → s ≠ 0 :=
fun {_} hs h => LT.lt.false (Complex.zero_re ▸ h ▸ hs)

open Complex EuclideanGeometry

/-Regular hexagon $A B C D E F$ has side length 2. A laser beam is fired inside the hexagon from point $A$ and hits $\overline{B C}$ at point $G$. The laser then reflects off $\overline{B C}$ and hits the midpoint of $\overline{D E}$. Find $B G$.-/
theorem geometry_608608 {A B C D E F G : ℂ}
    (hexagon : A = 2 ∧ B = 1 + √3 * I ∧ C = -1 + √3 * I ∧ D = -2 ∧ E = -1 - √3 * I ∧ F = 1 - √3 * I)
    (hG : ∃ r : ℝ, -1 < r ∧ r < 1 ∧ G = r + √3 * I)
    (hrefl : ∠ A G B = ∠ C G ((D + E) / 2)) : dist B G = 2 / 5 := by
-- Extend the assumptions `hexagon` and `hG`
  rcases hexagon with ⟨hA, hB, hC, hD, hE, hF⟩
  rcases hG with ⟨r, ⟨rgt, rlt, hG⟩⟩
-- Rewrite the angles in `hrefl` to `Complex.arg` forms
  repeat rw [angle, angle_eq_abs_arg] at hrefl
  repeat rw [vsub_eq_sub] at hrefl
-- Substitute $A$, $B$, $C$, $D$, $E$ and $G$ in `hrefl` and simplify
  rw [hA, hB, hC, hD, hE, hG] at hrefl; ring_nf at hrefl
  have : -(r * (1 - (r:ℂ))⁻¹) - ↑√3 * I * (1 - (r : ℂ))⁻¹ + (1 - (r : ℂ))⁻¹ * 2 =
  (2 - r - √3 * I) * ((1 - r)⁻¹ : ℝ) := by push_cast; ring
-- Rewrite by `arg_mul_real` to remove the real denominators on both sides of `hrefl`
  rw [this, arg_mul_real] at hrefl; field_simp at hrefl
  rw [div_sub_div_same, ← neg_div_neg_eq] at hrefl
  ring_nf at hrefl; field_simp at hrefl; norm_cast at hrefl
  rw [div_eq_mul_inv] at hrefl; nth_rw 2 [mul_comm] at hrefl
  rw [arg_mul_real, abs_arg_inv] at hrefl
-- Apply `arg_of_im_neg`, `arg_of_im_pos` and to compute the arg's on two sides of `hrefl` respectively
  simp [arg_of_im_neg] at hrefl
  simp [arg_of_im_pos] at hrefl
  rw [abs_eq_self.mpr, abs_eq_self.mpr] at hrefl
-- Take a `Real.cos` on two sides of `hrefl` to remove the `Real.arccos`
  apply_fun fun t => Real.cos t at hrefl
  rw [Real.cos_arccos, Real.cos_arccos, ← sub_eq_add_neg] at hrefl
  rw [← pow_left_inj₀ _ _ (show 2≠0 by simp)] at hrefl
  rw [div_pow, div_pow] at hrefl
-- Compute the `Complex.abs` in `hrefl`
  replace this : Complex.abs (2 + (-r - √3 * I)) ^ 2 = (2 - r) ^ 2 + 3 := by
    rw [abs_eq_sqrt_sq_add_sq, Real.sq_sqrt]; simp; ring
    simp; positivity
  rw [this] at hrefl; replace this : Complex.abs (3 + r * 2 + √3 * I * 3) ^ 2 =
  (3 + 2 * r) ^ 2 + 27 := by
    rw [abs_eq_sqrt_sq_add_sq, Real.sq_sqrt, show √3 * I * 3 = 3 * √3 * I by ring]
    simp; ring_nf; norm_num; ring
    positivity
  rw [this] at hrefl; replace this : 0 < (2 - r) ^ 2 + 3 := by positivity
  have : 0 < (3 + 2 * r) ^ 2 + 27 := by positivity
-- Simplify `hrefl` to a quadratic equation in $r$ and solve for $r=3/5$
  rw [← sub_eq_zero] at hrefl; field_simp at hrefl; ring_nf at hrefl
  simp [show 81 - r * 144 + r ^ 2 * 15 = 3 * (5 * r - 3) * (r - 9) by ring] at hrefl
  rcases hrefl with hr|hr
  -- Substitute $B$ and $G$ in the goal to compute the final result
  · replace hr : r = 3 / 5 := by linarith only [hr]
    simp [hr] at hG; simp [dist_eq, hB, hG]; norm_num
  linarith only [hr, rlt]
-- Finish the rest trivial goals, mainly checking positivities
  · apply div_nonneg; linarith only [rlt]; positivity
  · apply div_nonneg; linarith only [rgt]; positivity
  · suffices : 0 ≤ (3 + r * 2) / Complex.abs (3 + ↑r * 2 + ↑√3 * I * 3)
    · linarith only [this]
    apply div_nonneg; linarith only [rgt]; positivity
  · rw [div_le_iff₀, one_mul, ← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)]
    rw [abs_eq_sqrt_sq_add_sq, Real.sq_sqrt, show √3 * I * 3 = 3 * √3 * I by ring]
    simp; any_goals positivity
    linarith only [rgt]
    rw [abs_eq_sqrt_sq_add_sq]; simp; positivity
  · suffices : 0 ≤ (2 + -r) / Complex.abs (2 + (-r - √3 * I))
    · linarith only [this]
    apply div_nonneg; linarith only [rlt]; positivity
  · rw [div_le_iff₀, one_mul, ← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)]
    rw [abs_eq_sqrt_sq_add_sq, Real.sq_sqrt]
    simp; any_goals positivity
    linarith only [rlt]
    rw [abs_eq_sqrt_sq_add_sq]; simp; positivity
  any_goals apply Real.arccos_nonneg
  · linarith only [rgt]
  · rw [inv_pos]; linarith only [rlt]
  · simp [hC, hG, sub_eq_zero, neg_eq_iff_add_eq_zero]
    norm_cast; linarith only [rgt]
  · simp [hD, hE, hG]; ring_nf
    rw [← ne_eq, ← neg_ne_zero]; ring_nf
    rw [show √3 * I * (3 / 2) = 3 / 2 * √3 * I by ring]
    apply ne_zero_of_re_pos; simp
    linarith only [rgt]
  · simp [hA, hG]; apply ne_zero_of_re_pos; simp
    linarith only [rlt]
  simp [hB, hG]; norm_cast; linarith only [rlt]