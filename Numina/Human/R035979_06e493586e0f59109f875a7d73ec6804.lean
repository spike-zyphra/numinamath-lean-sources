import Mathlib

/-- Suppose that x,y and z are three positive numbers that satisfy the equations
    xyz=1, x+1/z=5, and y+1/x=29. Then z+1/y=m/n, where m and n are relatively prime positive integers.
    Find m+n. -/
theorem algebra_97318 {x y z : ℝ} (m n : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) (hxz : x + 1 / z = 5) (hyx : y + 1 / x = 29)
    (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n) (eq : z + 1 / y = m / n) : m + n = 5 := by
  -- We can rewrite xyz = 1 as z = 1/(xy).
  rw[mul_comm, ← eq_div_iff_mul_eq (mul_pos hx hy).ne'] at hxyz
  -- Substituting into one of the given equations, we have
  -- x + xy = 5,
  rw[hxyz, div_div_cancel₀ (by simp)] at hxz
  -- x (1 + y) = 5, hence y = (5-x)/x.
  rw[Eq.comm, add_comm, ← sub_eq_iff_eq_add, Eq.comm, mul_comm, ← eq_div_iff_mul_eq hx.ne'] at hxz
  -- We can substitute back into y + 1/x = 29 to obtain
  -- (5 - x)/x + 1/x = 29,
  rw[hxz] at hyx
  -- or equivalently 5-x+1 = 29x,
  field_simp at hyx
  -- such that x = 1/5.
  have : x = 1/5 := by linarith
  -- Plugging this back in, we get y = 24,
  rw[this] at hxz hxyz
  norm_num at hxz
  rw[hxz] at hxyz eq
  -- z = 5/24,
  norm_num at hxyz
  -- and finally z + 1/y = m/n = 1/4.
  rw[hxyz] at eq
  norm_num at eq
  -- So m = 1, n = 4, m + n = 5.
  have : m = 1 ∧ n = 4 := by
    zify at hm hn ⊢
    apply Rat.div_int_inj (a := m) (b := n) (c := 1) (d := 4) hn (by norm_num)
    · simpa using hmn
    · norm_num
    · rify; rw[← eq]
  rw[this.1, this.2]