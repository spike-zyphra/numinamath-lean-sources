import Mathlib

/- Find all complex numbers $z$ such that
\[z^2 = -77 - 36i.\]Enter all complex numbers, separated by commas. -/
theorem algebra_14112 : {z : ℂ | z^2 = -77 - 36 * .I} = {2 - 9 * .I, -2 + 9 * .I} := by
  ext z
  simp
  constructor
  · intro h; apply or_iff_not_imp_right.mpr; intro h₁
    apply mul_left_cancel₀ (sub_ne_zero.mpr h₁)
    rw [← sub_eq_zero] at h ⊢
    ring_nf at h ⊢
    rw [← sub_eq_zero] at h ⊢
    simp_all [Complex.ext_iff]
    nlinarith
  · rintro (rfl | rfl) <;> ring_nf <;> simp [Complex.ext_iff]
    <;> nlinarith
