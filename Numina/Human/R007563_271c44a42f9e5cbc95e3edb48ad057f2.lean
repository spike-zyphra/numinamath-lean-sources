import Mathlib

/-- There are integers a,b and c each greater than 1, such that
    $\sqrt[a]{N\sqrt[b]{N \sqrt[c] N}} = \sqrt[36]{N^25}$
    for all N≠1. What is b?
    (A) 2(B) 3(C) 4(D) 5(E) 6 -/
theorem algebra_93459 {a b c : ℕ} (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (h : ∀ N : ℝ, N ≠ 1 → (N * (N * (N ^ (1 / c : ℝ))) ^ (1 / b : ℝ)) ^ (1 / a : ℝ) = N ^ (25 / 36 : ℝ)) :
    b = 3 := by
  -- $\sqrt[a]{N\sqrt[b]{N \sqrt[c] N}}$ can be simplified to $N^{1/a +1/(ab) + 1/(abc)}$.
  have : ∀ N : ℝ, N > 0 → N ≠ 1 → (N * (N * (N ^ (1 / c : ℝ))) ^ (1 / b : ℝ)) ^ (1 / a : ℝ) = N^(1 / (a : ℝ) + 1 / (a * b) + 1 / (a * b * c)) := by
    intro N pos eq
    rw[Real.mul_rpow pos.le (by positivity), ← Real.rpow_mul (by positivity)]
    conv => lhs; rhs; lhs; lhs; rw[← Real.rpow_one N]
    rw[← Real.rpow_add pos, ← Real.rpow_mul (by positivity), ← Real.rpow_add pos]
    congr 1
    field_simp
    ring
  -- The equation is then $N^{1/a +1/(ab) + 1/(abc)} = N^{25/36}$,
  have eq1 (N) pos neq := (this N pos neq).symm.trans $ h N neq
  specialize eq1 2 (by positivity) (by norm_num)
  -- which implies that $1/a +1/(ab) + 1/(abc) = 25/36$.
  rw[← Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by positivity)] at eq1
  simp only [Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true, Real.logb_rpow, one_div,
    mul_inv_rev] at eq1
  -- a has to be 2, since the term is monotonically decreasing in a,b,c
  have : a = 2 := by
    symm
    rw[eq_iff_not_lt_of_le ha]
    intro lt
    -- and $25/36 > 7/12 7/12$ is the result when $a = 3, b = 2, c = 2$.
    have : (a : ℝ)⁻¹ + (↑b)⁻¹ * (↑a)⁻¹ + (↑c)⁻¹ * ((↑b)⁻¹ * (↑a)⁻¹) < 22 / 36 := by
      have a3 : 3 ≤ a := lt
      have : 2 ≤ b := hb
      have : 2 ≤ c := hc
      have ainv : (a : ℝ)⁻¹ ≤ 3 ⁻¹ := (inv_le_inv₀ (by positivity) (by positivity)).mpr (by assumption_mod_cast)
      have binv : (b : ℝ)⁻¹ ≤ 2 ⁻¹ := (inv_le_inv₀ (by positivity) (by positivity)).mpr (by assumption_mod_cast)
      have cinv : (c : ℝ)⁻¹ ≤ 2 ⁻¹ := (inv_le_inv₀ (by positivity) (by positivity)).mpr (by assumption_mod_cast)
      have : (a : ℝ)⁻¹ + (↑b)⁻¹ * (↑a)⁻¹ + (↑c)⁻¹ * ((↑b)⁻¹ * (↑a)⁻¹) ≤ 3 ⁻¹ + 2 ⁻¹ * 3 ⁻¹ + 2 ⁻¹ * (2 ⁻¹ * 3 ⁻¹) := by
        apply add_le_add
        · apply add_le_add ainv (mul_le_mul binv ainv (by positivity) (by positivity))
        · apply mul_le_mul cinv (mul_le_mul binv ainv (by positivity) (by positivity)) (by positivity) (by positivity)
      apply lt_of_le_of_lt this
      norm_num
    rw[← eq1] at this
    norm_num at this
  rw[this] at eq1
  have fraction : 7 / 18 = (b : ℝ)⁻¹ + (↑c)⁻¹ * (↑b)⁻¹ := by linarith
  -- b being 2 will make the fraction too large,
  have bne : b ≠ 2 := by
    rintro rfl
    have : - 2 / 18 = (↑c : ℝ)⁻¹ * (↑ 2)⁻¹ := by linarith
    have : -2/(18 : ℝ) > 0 := by rw[this]; positivity
    norm_num at this
  -- b >= 4 will make it too small.
  -- b being 3 will make the fraction 2/3 which is close to 25/36,
  -- and with c being 6, it becomes 25/36.
  have blt : b < 4 := by
    rw[← not_le]
    intro le
    have binv : (b : ℝ)⁻¹ ≤ 4 ⁻¹ := (inv_le_inv₀ (by positivity) (by positivity)).mpr (by assumption_mod_cast)
    have cinv : (c : ℝ)⁻¹ ≤ 2 ⁻¹ := (inv_le_inv₀ (by positivity) (by positivity)).mpr (by assumption_mod_cast)
    have : (b : ℝ)⁻¹ + (c : ℝ)⁻¹ * (b : ℝ)⁻¹ ≤ 4 ⁻¹ + 2 ⁻¹ * 4 ⁻¹ := add_le_add binv
      (mul_le_mul cinv binv (by positivity) (by positivity))
    rw[← fraction] at this
    norm_num at this
  omega