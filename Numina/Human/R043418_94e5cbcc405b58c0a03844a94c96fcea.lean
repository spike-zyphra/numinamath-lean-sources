import Mathlib


/- 2. Solve the equation $\left(\frac{x}{243}\right)^{\log _{2}\left(\frac{9 x}{4}\right)}=\frac{729}{x^{4}}$. -/
theorem algebra_149236 {x : ℝ} (hx : 0 < x ∧ x ≠ 1) :
    (x / 243) ^ Real.logb 2 (9 * x / 4) = 729 / x ^ 4 ↔
    x = 243 / 4 ∨ x = 1 / 9 := by
  constructor
  · intro h
    -- let's take logb 2 of both sides
    apply congr_arg (fun x => Real.logb 2 x) at h
    rw [Real.logb_rpow_eq_mul_logb_of_pos (by linarith), Real.logb_div (by linarith) (by norm_num), Real.logb_div (by linarith) (by norm_num), Real.logb_div (by norm_num) (by simp; linarith), Real.logb_mul (by norm_num) (by linarith), Real.logb_pow, show (729:ℝ)=3^6 by norm_num, show (243:ℝ)=3^5 by norm_num, Real.logb_pow, Real.logb_pow, show (4:ℝ)=2^2 by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one,  show (9:ℝ)=3^2 by norm_num, Real.logb_pow] at h
    -- let a = Real.logb 2 3 and y = Real.logb 2 x
    let q:∃ y:ℝ, y = Real.logb 2 x := by
      simp only [exists_eq]
    obtain ⟨y, ydef⟩ := q
    let q:∃ a:ℝ, a = Real.logb 2 3 := by
      simp only [exists_eq]
    obtain ⟨a, adef⟩ := q
    -- rewrite h in a y
    rw [← adef, ← ydef] at h
    -- simple quadratic
    ring_nf at h
    apply congr_arg (fun x => x - (a * 6 - y * 4)) at h
    ring_nf at h
    -- we can solve for y
    have sol := (quadratic_eq_zero_iff (a:=(1:ℝ)) (b:=-3*a+2) (c:=4*a-10*a^2) (by norm_num) (s:=7*a-2) (by unfold discrim; ring_nf) y).mp
    simp at sol
    have hsol:a * 4 + (-(a * y * 3) - a ^ 2 * 10) + y * 2 + y ^ 2 = y * y + (-(3 * a) + 2) * y + (4 * a - 10 * a ^ 2) := by ring_nf
    rw [← hsol, h] at sol; simp at sol; ring_nf at sol
    -- we analyze both possible solutions
    cases' sol with sol1 sol2
    · rw [ydef, Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) hx.1, adef, Real.rpow_add (by norm_num), Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)] at sol1; norm_num at sol1
      left; linarith
    · rw [ydef, Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) hx.1, adef, Real.rpow_neg (by norm_num), Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)] at sol2
      ring_nf at sol2; right; linarith
  · -- the other side is just simple case verification
    intro h
    cases' h with h1 h2
    · rw [h1]; ring_nf
      calc ((1:ℝ) / 4) ^ Real.logb 2 (2187 / 16)
      _ = (4 ^ Real.logb 2 (2187 / 16))⁻¹ := by rw [Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow]; ring_nf
      _ = (((2:ℝ)^(2:ℝ)) ^ Real.logb 2 (2187 / 16))⁻¹ := by ring_nf
      _ = (2^(2 * Real.logb 2 (2187 / 16)))⁻¹ := by rw [← Real.rpow_mul (by norm_num)]
      _ = (2^(Real.logb 2 (2187 / 16) * 2))⁻¹ := by ring_nf
      _ = (((2:ℝ) ^ Real.logb 2 (2187 / 16))^(2:ℝ))⁻¹ := by rw [Real.rpow_mul (by norm_num)]
      _ = ((2187 / 16) ^ 2)⁻¹ := by rw [Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]; ring_nf
      _ = 256 / 4782969 := by ring_nf
    · rw [h2]; ring_nf
      rw [Real.logb_div (by norm_num) (by norm_num), show (4:ℝ)=2^2 by norm_num, Real.logb_pow]; simp; norm_num