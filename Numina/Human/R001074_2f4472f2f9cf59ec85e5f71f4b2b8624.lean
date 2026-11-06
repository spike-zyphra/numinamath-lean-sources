import Mathlib

/- Let $a$ and $b$ be nonzero complex numbers such that
\[|a| = |b| = |a + b|.\]Find the sum of all possible values of $\frac{a}{b}.$ -/
theorem algebra_20326:
  ∑ᶠ z ∈ {z:ℂ | ∃(a b: ℂ),  z = a/b ∧ a ≠ 0 ∧ b ≠ 0 ∧
      (‖a‖ = ‖b‖ ∧ ‖a‖ = ‖a + b‖)}, z = -1 := by
  -- from |a| = |b| = |a+b|, we have (a+b)(1/a+1/b)=1
  have h1: ∀(a b:ℂ), a ≠ 0 → b ≠ 0 → (‖a‖ = ‖b‖ ∧ ‖a‖ = ‖a + b‖)
    → (a+b) * (1/a + 1/b) = 1 := by
    intro a b anz bnz hab
    -- denote their norm as r.
    let r : ℝ := ‖a‖
    have r_def: r = ‖a‖ := rfl
    -- a * conja = normsq = r^2
    have conja: (starRingEnd ℂ) a = ↑(r^2)/a := by
      rw [r_def]
      rw [← Complex.normSq_eq_norm_sq]
      rw [Complex.normSq_eq_conj_mul_self]
      simp [anz]
    -- also, b * conjb = r^2
    have conjb: (starRingEnd ℂ) b = ↑(r^2)/b := by
      rw [r_def, hab.left]
      rw [← Complex.normSq_eq_norm_sq]
      rw [Complex.normSq_eq_conj_mul_self]
      simp [bnz]
    -- (a+b)(1/a+1/b) = (a+b)(r^2/a+r^2/b)r^2
    have hh1: (a+b) * (1/a+1/b) = (a+b) * (↑(r^2)/a + ↑(r^2)/b)
      / r^2 := by
      have tt1: (r^2:ℂ) ≠ 0 := by
        rw [r_def]; simp [anz]
      have tt2: (a+b) * (1/a+1/b) =  (a+b) * (1/a+1/b)
        * r^2 / r^2 := by
        symm; exact mul_div_cancel_right₀ ((a + b) * (1 / a + 1 / b)) tt1
      have tt3: (a + b) * (1 / a + 1 / b) * r ^ 2 =
        (a+b) * (r^2/a+r^2/b) := by
        have: (1/a+1/b)*r^2 = r^2/a+r^2/b := by ring
        rw [mul_assoc, this]
      rw [tt2, tt3]; simp
    rw [hh1, ← conja, ← conjb]
    -- notice that (a+b) * (conja + conjb) = r^2
    have hh2: (starRingEnd ℂ) a + (starRingEnd ℂ) b =
      (starRingEnd ℂ) (a+b) := by
      exact Eq.symm (RingHom.map_add (starRingEnd ℂ) a b)
    rw [hh2, mul_comm, ← Complex.normSq_eq_conj_mul_self]
    rw [Complex.normSq_eq_norm_sq]
    rw [← hab.right, r_def]
    simp [anz]
  -- if we let z=a/b, then (a+b)(1/a+1/b)=1 simplifies to z^2+z+1=0
  have h2: ∀(a b:ℂ), a ≠ 0 → b ≠ 0 → (a+b)*(1/a+1/b) = 1 →
    (a/b)^2+(a/b)+1 = 0 := by
    intro a b anz bnz hab
    have hh1: (a+b)*(1/a+1/b) = a/b+1/(a/b)+2 := by
      field_simp [anz,bnz]
      ring
    have hh2: (a/b) + 1/(a/b) + 1 = 0 := by
      rw [hh1] at hab
      have: (0:ℂ) = 1-1 := by simp
      rw [this]
      nth_rw 3 [← hab]; ring
    have hh3: (a/b)^2+(a/b)+1 = (a/b) * ((a/b)+1/(a/b)+1) := by
      field_simp [anz, bnz]; ring
    rw [hh3, hh2]; simp
  -- solve the equation, a/b is determined. in fact, we can use vieta's formula to get sum of two roots, instead of finding them out.
  have h3: ∀(a b:ℂ), a ≠ 0 → b ≠ 0 → (a+b)*(1/a+1/b) = 1 →
    (a/b) = -1/2+(√3/2)*Complex.I ∨ (a/b) = -1/2-(√3/2)*Complex.I := by
    intro a b anz bnz hab
    have eq1 := h2 a b anz bnz hab
    have eq2: 1*((a/b)*(a/b))+1*(a/b)+1 = 0 := by
      rw [← eq1]; ring
    have hh1: discrim 1 1 1 = (√3*Complex.I)*(√3*Complex.I) := by
      rw [discrim]; simp; ring_nf; simp
      norm_cast; simp
    have hh2: (1:ℂ) ≠ 0 := by norm_num
    have := (quadratic_eq_zero_iff hh2 hh1 (a/b)).mp eq2
    rcases this with hl | hr
    · left; rw [hl]; ring
    · right; rw[hr]; ring
  -- thus set s only contain these two solutions.
  have h4: {z:ℂ | ∃(a b: ℂ),  z = a/b ∧ a ≠ 0 ∧ b ≠ 0 ∧
      (‖a‖ = ‖b‖ ∧ ‖a‖ = ‖a + b‖)} = {(-1/2+(√3/2)*Complex.I), (-1/2-(√3/2)*Complex.I)} := by
    ext z; simp
    constructor <;> intro h
    · rcases h with ⟨a,b,hab'⟩
      rcases hab' with ⟨zeq, anz, bnz, hab⟩
      rw [zeq]
      apply h3 a b anz bnz
      apply h1 a b anz bnz hab
    · have anz: (1/2 + √3/2 * Complex.I) ≠ 0 := by
        apply ne_of_apply_ne Complex.re (by simp)
      have bnz: (1/2 - √3/2 * Complex.I) ≠ 0 := by
        apply ne_of_apply_ne Complex.re (by simp)
      have aabs: Complex.abs (1/2 + √3/2 * Complex.I) = 1 := by
        have tt1: Complex.normSq (1/2 + √3/2 * Complex.I) = 1 := by
          apply Complex.ofReal_inj.mp
          rw [Complex.normSq_apply]
          simp; field_simp; norm_cast; simp; ring
        have tt2: Complex.abs (1/2 + √3/2 * Complex.I) =
          √ (Complex.normSq (1/2 + √3/2 * Complex.I)) := by
          exact rfl
        rw [tt2, tt1]; simp
      have babs: Complex.abs (1/2 - √3/2 * Complex.I) = 1 := by
        have tt1: Complex.normSq (1/2 - √3/2 * Complex.I) = 1 := by
          apply Complex.ofReal_inj.mp
          rw [Complex.normSq_apply]
          simp; field_simp; norm_cast; simp; ring
        have tt2: Complex.abs (1/2 - √3/2 * Complex.I) =
          √ (Complex.normSq (1/2 - √3/2 * Complex.I)) := by
          exact rfl
        rw [tt2, tt1]; simp
      rcases h with hl | hr
      · -- -1/2 + √3/2i = e^i(2/3π, we choose a,b such that their argument difference is 2/3π)
        have hz: z = (1/2 + √3/2 * Complex.I) / (1/2 - √3/2 * Complex.I)
          := by
          have: 1 - √3*Complex.I ≠ 0 := by
            apply ne_of_apply_ne Complex.re (by simp)
          rw [hl]
          field_simp [this]; ring_nf
          simp [Complex.I_mul_I, pow_two]
          ring_nf; norm_cast; simp; ring
        use (1/2 + √3/2 * Complex.I)
        use (1/2 - √3/2 * Complex.I)
        simp at anz bnz aabs babs
        rw [hz]; simp [anz, bnz, aabs, babs]
        norm_cast; norm_num
      · -- -1/2-√3/2i is e^i(-2/3π), so we reverse a and b.
        have hz: z = (1/2-√3/2 * Complex.I) / (1/2+√3/2 * Complex.I)
          := by
          rw [hr]
          have: 1 + √3*Complex.I ≠ 0 := by
            apply ne_of_apply_ne Complex.re (by simp)
          field_simp [this]
          ring_nf
          simp [pow_two]; norm_cast; simp
          ring
        use (1/2 - √3/2 * Complex.I)
        use (1/2 + √3/2 * Complex.I)
        rw [hz]
        simp at *; simp [*]
        have: (2:ℂ)⁻¹+2⁻¹ = 1 := by ring
        rw [this]; simp
  -- so -1/2 + √3/2i + (-1/2 - √3/2i) = -1, answer is -1.
  rw [h4]
  have: -1/2 + √3/2*Complex.I ≠ -1/2 - √3/2 * Complex.I := by
    apply ne_of_apply_ne Complex.im
    simp; field_simp
    by_contra! hc
    have := eq_zero_of_neg_eq hc.symm
    norm_num at this
  rw [finsum_mem_pair this]; ring
