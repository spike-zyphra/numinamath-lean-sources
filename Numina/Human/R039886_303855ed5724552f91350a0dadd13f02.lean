import Mathlib

open Complex

/-Let $c$ be a complex number.  Suppose there exist distinct complex numbers $r$, $s$, and $t$ such that for every complex number $z$, we have
\[
  (z - r)(z - s)(z - t) = (z - cr)(z - cs)(z - ct).
\]Compute the number of distinct possible values of $c$.-/
theorem algebra_13625 {r s t : ℂ} (c : ℂ) (h₁ : r ≠ s) (h₂ : r ≠ t) (h₃ : s ≠ t)
    (hz: ∀ z, (z - r) * (z - s) * (z - t) = (z - c * r) * (z - c * s) * (z - c * t))
    : c = 1 ∨ c = -1 ∨ c = -1/2 + √3/2 * I ∨ c = -1/2 - √3/2 * I  := by

  have eq₃ (z : ℂ) : z^3 - (r + s + t) * z^2 + (r * s + s * t + t * r) * z - r * s * t = z^3 - c * (r + s + t) * z^2 + c^2 * (r * s + s * t + t * r) * z - c^3 * r * s * t := by
    -- Expanding both sides gives z^3 - (r+s+t)z^2 + (rs+st+rt)z - rst
    have eq₁ (z : ℂ) : (z - r) * (z - s) * (z - t) = z^3 - (r + s + t) * z^2 + (r * s + s * t + t * r) * z - r * s * t := by ring_nf
    -- z^3 - c(r+s+t)z^2 + c^2(rs+st+rt)z - c^3rst.
    have eq₂ (z : ℂ) : (z - c * r) * (z - c * s) * (z - c * t) = z^3 - c * (r + s + t) * z^2 + c^2 * (r * s + s * t + t * r) * z - c^3 * r * s * t := by ring_nf
    rw [(eq₁ z).symm]
    rw [(eq₂ z).symm]
    exact hz z

  -- Since this equation holds for all $z,$ we must have
  have coeff₃ : c^3 * r * s * t = r * s * t := by
    have := eq₃ 0
    simp at this
    simp
    rcases this with ((r₁ | r₂) | r₃)
    . apply Or.inl
      apply Or.inl
      exact r₁.symm
    . apply Or.inl
      apply Or.inr
      exact r₂
    . apply Or.inr
      exact r₃
  have eq₃ (z : ℂ) : (r + s + t) * z^2 - (r * s + s * t + t * r) * z = c * (r + s + t) * z^2 - c^2 * (r * s + s * t + t * r) * z := by
    have := eq₃ z
    rw [sub_add, sub_add, sub_sub, sub_sub, sub_right_inj, coeff₃] at this
    rw [add_left_inj] at this
    exact this

  have coeff₁: (r + s + t) = c * (r + s + t) := by
    have p := eq₃ 1
    have q := eq₃ (-1)
    simp only [one_mul, neg_one_mul, one_pow, neg_one_pow_two, mul_one] at p q
    rw [mul_neg_one, sub_neg_eq_add, mul_neg_one, sub_neg_eq_add] at q
    have {a b c d : ℂ} (h₁: a = b) (h₂: c = d) : a + c = b + d := h₁ ▸ h₂ ▸ rfl
    have := this p q
    rw [←add_assoc] at this
    rw (config := { occs := .pos [2]}) [add_comm] at this
    rw [add_sub, sub_add_cancel] at this
    rw [←add_assoc, ←add_assoc, ←add_assoc] at this
    rw (config := { occs := .pos [7]}) [add_comm] at this
    rw [add_sub, sub_add_cancel] at this
    rw [add_assoc, add_assoc, ←add_assoc r] at this
    rw [←two_mul, ←two_mul] at this
    simp at this
    exact this

  have coeff₂ : (r * s + s * t + t * r) = c^2 * (r * s + s * t + t * r) := by
    have p := eq₃ 1
    simp only [one_mul, one_pow, mul_one] at p
    rw [coeff₁.symm, sub_right_inj] at p
    exact p

  -- If none of $c, c^2, c^3$ are equal to $1,$ then these equations imply that \[r + s + t = rs + st + rt = rst = 0.\]
  by_cases h : c ≠ 1 ∧ c^2 ≠ 1 ∧ c^3 ≠ 1
  . have coeff₃ : (c^3 - 1) * (r * s * t) = 0 := by
      ring_nf
      rw [coeff₃, sub_self]
    simp at coeff₃
    rcases coeff₃ with (r₁ | r₃)
    . -- r₁: c^3 - 1 = 0, which is a contradiction
      have := h.2.2
      rw [sub_eq_zero] at r₁
      rw [r₁] at this
      absurd this
      exact rfl

    -- r₃: r * s * t = 0
    have coeff₁ : (c - 1) * (r + s + t) = 0 := by
      rw [sub_mul, coeff₁.symm]
      ring_nf
    simp at coeff₁
    rcases coeff₁ with (r₁ | r₁)
    . -- r₁: c - 1 = 0, which is a contradiction
      have := h.1
      rw [sub_eq_zero] at r₁
      rw [r₁] at this
      absurd this
      exact rfl

    -- r₁: r + s + t = 0
    have coeff₂ : (c^2 - 1) * (r * s + s * t + t * r) = 0 := by
      rw [sub_mul, coeff₂.symm]
      ring_nf
    simp at coeff₂
    rcases coeff₂ with (r₁ | r₂)
    . -- r₁: c^2 - 1 = 0, which is a contradiction
      have := h.2.1
      rw [sub_eq_zero] at r₁
      rw [r₁] at this
      absurd this
      exact rfl

    -- r₂: r * s + s * t + t * r = 0
    rcases r₃ with ((h1 | h2) | h3)
    . -- r = 0
      rw [h1] at r₁ r₂
      simp at r₁ r₂
      rcases r₂ with (h4 | h5)
      . -- s = 0
        rw [h4, h1] at h₁
        absurd h₁
        rfl
      . -- t = 0
        rw [h5, h1] at h₂
        absurd h₂
        rfl
    . -- s = 0
      rw [h2] at r₁ r₂
      simp at r₁ r₂
      rcases r₂ with (h4 | h5)
      . -- t = 0
        rw [h4, h2] at h₃
        absurd h₃
        rfl
      . -- r = 0
        rw [h5, h2] at h₁
        absurd h₁
        rfl
    . -- t = 0
      rw [h3] at r₁ r₂
      simp at r₁ r₂
      rcases r₂ with (h4 | h5)
      . -- r = 0
        rw [h4, h3] at h₂
        absurd h₂
        rfl
      . -- s = 0
        rw [h5, h3] at h₃
        absurd h₃
        rfl

  by_cases r₁ : c = 1
  . exact Or.inl r₁
  simp at r₁ h
  have h := h r₁
  by_cases r₂ : c^2 = 1
  . have : (c - 1) * (c + 1) = 0 := by
      ring_nf
      rw [r₂]
      simp
    simp at this
    rcases this with (r₂ | r₃)
    . -- c - 1 = 0
      rw [sub_eq_zero] at r₂
      exact Or.inl r₂
    . -- c + 1 = 0
      rw [←sub_neg_eq_add, sub_eq_zero] at r₃
      apply Or.inr
      apply Or.inl
      exact r₃
  simp at r₂
  have h := h r₂.2
  -- c ^ 3 = 1
  have : (c - 1) * (c^2 + c + 1) = 0 := by
    ring_nf
    rw [h]
    ring_nf
  simp at this
  rcases this with (r₂ | r₃)
  . -- c - 1 = 0
    rw [sub_eq_zero] at r₂
    exact Or.inl r₂
  have : (c - (-1/2 + √3/2 * I)) * (c - (-1/2 - √3/2 * I)) = c ^ 2 + c + 1 := by
    ring_nf
    rw [Complex.I_sq]
    have : (√3 : ℂ)^2 = 3 := by
      norm_cast
      rw [Real.sq_sqrt (by linarith)]
    rw [this]
    ring_nf
  rw [r₃] at this
  simp at this
  rcases this with (r₄ | r₅)
  . -- c - (-1/2 + √3/2 * I) = 0
    rw [sub_eq_zero] at r₄
    apply Or.inr
    apply Or.inr
    apply Or.inl
    exact r₄
  . -- c - (-1/2 - √3/2 * I) = 0
    rw [sub_eq_zero] at r₅
    apply Or.inr
    apply Or.inr
    apply Or.inr
    exact r₅
