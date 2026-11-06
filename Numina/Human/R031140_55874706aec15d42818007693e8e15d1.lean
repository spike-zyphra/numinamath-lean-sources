import Mathlib

open Real

/- 4. Solve the system


$$

\left\{\begin{array}{l}
\log _{y} x-2 \log _{x} y=1 \\
x-y=2
\end{array}\right.

$$
 -/
theorem algebra_213623 {x y : ℝ} (hx : 0 < x ∧ x ≠ 1) (hy : 0 < y ∧ y ≠ 1)
    (h1 : logb y x - 2 * logb x y = 1) (h2 : x - y = 2) :
    x = 4 ∧ y = 2 ∨ x = sqrt 2 + 1 ∧ y = sqrt 2 - 1 := by
    obtain ⟨hx0, hx1⟩ := hx
    obtain ⟨hy0, hy1⟩ := hy
    -- let t = logb x y
    let q:∃ t:ℝ, t = logb y x := by
      use logb y x
    obtain ⟨t, tdef⟩ := q
    rw [← tdef, ← inv_logb, ← tdef] at h1
    -- quadratic to solve, but first need to show t≠0
    have h3: t ≠ 0 := by
      rw [tdef]
      simp
      exact ⟨by linarith, ⟨by assumption, ⟨by linarith, ⟨by linarith, ⟨by assumption, by linarith⟩⟩⟩⟩⟩
    apply congr_arg (fun x=>t*x - t) at h1
    conv_lhs at h1 =>
      calc _
      _ = t * t - 2 * (t * t⁻¹) - t := by ring_nf
      _ = t * t - 2 - t:= by rw [mul_inv_cancel₀ h3]; ring_nf
    ring_nf at h1
    -- now we have a quadratic in t
    have sol := (quadratic_eq_zero_iff (a:=(1:ℝ)) (b:=(-1:ℝ)) (c:=(-2:ℝ)) (by norm_num) (s:=3) (by unfold discrim; norm_num) t).mp
    ring_nf at sol
    specialize sol h1
    -- now we have two quite trivial cases
    cases' sol with sol' sol'
    · rw [tdef, logb_eq_iff_rpow_eq (by assumption) (by assumption) (by assumption)] at sol';
      rw [← sol'] at h2
      apply congr_arg (fun x => x - 2) at h2
      have sol := (quadratic_eq_zero_iff (a:=(1:ℝ)) (b:=(-1:ℝ)) (c:=(-2:ℝ)) (by norm_num) (s:=3) (by unfold discrim; norm_num) y).mp
      ring_nf at sol;
      conv_lhs at h2 =>
        calc _
        _ = y ^ 2 - y - 2 := by norm_cast
        _ = -2 - y + y ^ 2 := by ring_nf
      simp at h2
      specialize sol h2
      cases' sol with sol'' sol''
      · left
        exact ⟨by rw [← sol', sol'']; norm_num, sol''⟩
      · linarith
    · rw [tdef, logb_eq_iff_rpow_eq (by assumption) (by assumption) (by assumption)] at sol';
      have h2':x = 2+y := by linarith
      rw [← sol'] at h2
      apply congr_arg (fun x => y * (x - 2)) at h2
      conv_lhs at h2 =>
        calc _
        _ = y * y ^ (-1:ℝ) - y^2 - 2*y := by ring_nf
        _ = y * y⁻¹ - 2 * y - y^2 := by rw [Real.rpow_neg_one]; ring_nf
        _ = 1 - 2 * y - y^2 := by rw [mul_inv_cancel₀ (by linarith)]
      simp at h2
      have sol := (quadratic_eq_zero_iff (a:=(-1:ℝ)) (b:=(-2:ℝ)) (c:=(1:ℝ)) (by norm_num) (s:=√8) (by unfold discrim; norm_num) y).mp
      ring_nf at sol h2
      specialize sol h2
      cases' sol with sol'' sol''
      · suffices y< 0 by linarith
        rw [sol'']
        apply add_neg
        norm_num
        apply mul_neg_of_pos_of_neg
        simp; norm_num
      · right
        conv_rhs at sol'' =>
          calc _
          _ = -1 + √(2^2*2) * (1 / 2) := by ring_nf
          _ = -1 + √(2^2) * √2 * (1 / 2) := by rw [Real.sqrt_mul (by norm_num)]
          _ = -1 + 2 * √2 * (1 / 2) := by rw [Real.sqrt_sq (by norm_num)]
          _ = -1 + √2 := by ring_nf
        ring_nf at sol'' ⊢
        exact ⟨by rw [h2', sol'']; ring_nf, sol''⟩