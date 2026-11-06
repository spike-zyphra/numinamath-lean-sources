import Mathlib
open Complex

/- 5. Let $a, b, c$ and $d$ be complex numbers. If the set $S=\{a, b, c, d\}$ has the property “for any $x, y \in S$, there must be $x y \in S$”, then when $a^{2}=1, b^{2}=1, c^{2}=b$, $b+c+d=$ $\qquad$ . -/
theorem algebra_106369 (a b c d : ℂ) (h0 : a≠b∧a≠c∧a≠d∧b≠c∧b≠d∧c≠d) (h1 : ∀ x y, x ∈ ({a, b, c, d}:Set ℂ) → y ∈ ({a, b, c, d}:Set ℂ) → x * y ∈ ({a, b, c, d}:Set ℂ)) (h2 : a^2 = 1) (h3 : b^2 = 1) (h4 : c^2 = b) : b + c + d = -1 := by -- It is necessary to explicitly have the condition that a, b, c, and d are not equal to each other, because the set in Lean4 will automatically deduplicate, while the original meaning implies that a, b, c, and d are not equal to each other
  obtain ⟨hab,hac,had,hbc,hbd,hcd⟩ := h0
  simp at h2 h3
  have hb : b = -1 := by
    match h3 with
    | Or.inl h => -- b = 1
      rw [h] at hab h4
      simp [hab] at h2
      simp at h4
      match h4 with
      | Or.inl hc1 => -- c = 1
        rw [←hc1] at h
        contradiction
      | Or.inr hc2 => -- c = -1
        rw [←hc2] at h2
        contradiction
    | Or.inr h => exact h -- b = -1
  rw [hb] at hab
  simp [hab] at h2
  rw [hb] at h4
  have h5 : c=I∧d=-I∨c=-I∧d=I := by
    rw [show -1=I^2 by simp] at h4
    have h4 := sq_eq_sq_iff_eq_or_eq_neg.1 h4
    have hi1 : -I ≠ 1 := by
      intro h
      have : (-I).re = (1:ℂ).re := by rw [h]
      norm_num at this
    have hi2 : I ≠ 1 := by
      intro h
      have : I.re = (1:ℂ).re := by rw [h]
      norm_num at this
    have hi3 : -I ≠ I := by
      intro h
      have : (-I).im = I.im := by rw [h]
      norm_num at this
    have hi4 : I ≠ -1 := by
      intro h
      have : (I).re = (-1:ℂ).re := by rw [h]
      norm_num at this
    match h4 with
    | Or.inl h4 => -- c = I
      apply Or.intro_left
      simp [h4]
      have := h1 (-1) I
      rw [h2,hb,h4] at this
      simp [hi1,hi2,hi3] at this
      exact this.symm
    | Or.inr h4 => -- c = -I
      apply Or.intro_right
      simp [h4]
      have := h1 (-1) (-I)
      rw [h2,hb,h4] at this
      simp at this
      simp [hi2,hi4,hi3.symm] at this
      exact this.symm
  match h5 with
  | Or.inl h51 =>
    obtain ⟨h6,h7⟩ := h51
    rw [hb,h6,h7]
    simp
  | Or.inr h52 =>
    obtain ⟨h6,h7⟩ := h52
    rw [hb,h6,h7]
    simp
