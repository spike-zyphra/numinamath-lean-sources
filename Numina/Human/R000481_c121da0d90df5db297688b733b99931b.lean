import Mathlib

open ComplexConjugate
open Complex

/-The equation of the line joining the complex numbers $-2 + 3i$ and $1 + i$ can be expressed in the form
\[az + b \overline{z} = 10\]for some complex numbers $a$ and $b$.  Find the product $ab$.-/
theorem algebra_11206 {a b u v : ℂ}
    (hu: u = -2 + 3 * I) (hv: v = 1 + I)
    (hab: ∀z, (z.im - v.im) * (z.re - u.re) = (z.re - v.re) * (z.im - u.im) → a * z + b * conj z = 10) : a * b = 13 := by
  -- Let $u = -2 + 3i$ and $v = 1 + i$, and let $z$ lie on the line joining $u$ and $v.$
  -- Then \[\frac{z - u}{v - u}\]is real.
  -- But a complex number is real if and only if it is equal to its conjugate, which gives us the equation
  -- \[\frac{z - u}{v - u} = \frac{\overline{z} - \overline{u}}{\overline{v} - \overline{u}}.\]


  have eq : ∀ z, ((z - u)/(v - u)).im = 0 → (a - (2 - 3 * I)) * z = (2 + 3 * I - b) * conj z := by
    intro z hz
    have : ((z - u)/(v - u)) = ((conj z - conj u)/(conj v - conj u)) := by
      have : ((conj z - conj u)/(conj v - conj u)) = conj ((z - u)/(v - u)) := by
        simp
      rw [this]
      exact Eq.symm ((fun {z} ↦ conj_eq_iff_im.mpr) hz)
    -- Substituting $u = -2 + 3i$ and $v = 1 + i$, we get \frac{z + 2 - 3i}{3 - 2i} = \frac{\overline{z} + 2 + 3i}{3 + 2i}.
    rw [hu, hv, ←star_def, star_add, ←sub_sub, ←sub_sub, ←sub_sub] at this
    rw [star_add, ←sub_sub, star_mul, star_def, conj_I] at this
    simp at this
    have : (2 - 3 * I) * z + (2 + 3 * I) * conj z  = 10 := by
      rw [(by exact conj_eq_iff_re.mpr rfl: conj (2 : ℂ) = 2)] at this
      rw [(by exact conj_eq_iff_re.mpr rfl: conj (3 : ℂ) = 3)] at this

      have h: 1 + I + 2 - 3 * I ≠ 0 := by
        apply ne_zero_of_one_lt_re
        simp
      have h': 1 + -I + 2 + I * 3 ≠ 0 := by
        apply ne_zero_of_one_lt_re
        simp
      -- Cross-multiplying, we get (3 + 2i)(z + 2 - 3i) = (3 - 2i)(\overline{z} + 2 + 3i).
      apply (div_eq_div_iff h h').mp at this
      -- This simplifies to (3 + 2i) z + (-3 + 2i) = 10i.
      apply Complex.ext_iff.mp at this
      apply And.right at this
      field_simp at this
      ring_nf at this
      apply Complex.ext_iff.mpr
      simp
      constructor
      . -- 2 * z.re + 3 * z.im + (2 * z.re + 3 * z.im) = 10
        ring_nf
        linarith
      . ring_nf

    have : (a * z + b * conj z) - ((2 - 3 * I) * z + (2 + 3 * I) * conj z) = 0 := by
      rw [this]
      specialize hab z
      have : (z.im - v.im) * (z.re - u.re) = (z.re - v.re) * (z.im - u.im) := by
        have : ∃(r : ℝ), (z - u) / (v - u) = r := by
          use ((z - u) / (v - u)).re
          apply Complex.ext_iff.mpr
          simp
          exact hz
        rcases this with ⟨r, hr⟩
        have : z = r * (v - u) + u := by
          rw [hr.symm, div_mul, div_self, div_one]
          simp
          rw [hu, hv]
          apply ne_zero_of_one_lt_re
          simp
        rw [this]
        simp
        ring_nf
      specialize hab this
      rw [hab, sub_self]

    rw [←sub_sub, add_sub_right_comm, ←sub_mul] at this
    rw [←add_sub, ←sub_mul, ←sub_neg_eq_add, sub_eq_zero, ←neg_mul] at this
    rw [neg_sub] at this
    exact this

  have e₁ := eq u (by simp)
  have : ((v - u)/(v - u)).im = 0 := by
    rw [hu, hv, div_self]
    simp
    apply ne_zero_of_one_lt_re
    simp
  have e₂ := eq v this
  by_cases ha: a = 2 - 3 * I
  . rw [ha, sub_self, zero_mul] at e₁
    simp at e₁
    obtain (hb | hb) := Or.symm e₁
    . -- u = 0
      rw [hu] at hb
      apply Complex.ext_iff.mp at hb
      obtain ⟨l, r⟩ := hb
      simp at l r
    rw [sub_eq_zero] at hb
    rw [hb.symm, ha]
    apply Complex.ext_iff.mpr
    norm_num

  -- now, we prove that, if a ≠ 2 - 3 * I, it will cause a contradiction
  have ha₁: a - (2 - 3 * I) ≠ 0 := by exact sub_ne_zero_of_ne ha
  have hb₁: 2 + 3 * I - b ≠ 0 := by
    intro hb
    rw [hb] at e₁
    simp at e₁
    obtain (hb | hb) := Or.symm e₁
    . -- u = 0
      rw [hu] at hb
      apply Complex.ext_iff.mp at hb
      obtain ⟨l, r⟩ := hb
      simp at l r
    absurd hb
    exact ha₁
  rw [mul_comm] at e₁ e₂
  have hu': conj u ≠ 0 := by
    have : u ≠ 0 := by
      intro hu'
      rw [hu'] at hu
      apply Complex.ext_iff.mp at hu
      obtain ⟨l, r⟩ := hu
      simp at l r
    exact (map_ne_zero (starRingEnd ℂ)).mpr this
  have hv': conj v ≠ 0 := by
    have : v ≠ 0 := by
      intro hv'
      rw [hv'] at hv
      apply Complex.ext_iff.mp at hv
      obtain ⟨l, r⟩ := hv
      simp at l r
    exact (map_ne_zero (starRingEnd ℂ)).mpr this
  apply (div_eq_div_iff hu' ha₁).mpr at e₁
  apply (div_eq_div_iff hv' ha₁).mpr at e₂
  rw [e₁.symm] at e₂
  apply (div_eq_div_iff hv' hu').mp at e₂
  rw [hu, hv] at e₂
  apply Complex.ext_iff.mp at e₂
  simp at e₂
  absurd e₂
  linarith
