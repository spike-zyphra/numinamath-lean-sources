import Mathlib

open Real

/- ## Task 27/80

All real numbers $x$ are to be determined for which the function is minimal

$$
f(x)=\sqrt{x+4 \sqrt{x-4}}+\sqrt{x-4 \sqrt{x-4}}
$$-/
theorem algebra_158581 {f : ℝ → ℝ} (hf : f = fun x => √(x + 4 * √(x - 4)) + √(x - 4 * √(x - 4))) (domain : Set ℝ)
    (hd : domain = {x : ℝ | x - 4 ≥ 0 ∧ x + 4 * √(x - 4) ≥ 0 ∧ x - 4 * √(x - 4) ≥ 0}) : {x : ℝ | x ∈ domain ∧ IsMinOn f domain x} = Set.Icc 4 8 := by
  -- Es gilt die Identität
  -- $$ x \pm 4 \sqrt{x-4} \equiv(2 \pm \sqrt{x-4})^{2} $$
  have h₁ {x : ℝ} (hx : x ∈ domain) : x + 4 * √(x - 4) = (2 + √(x - 4)) ^ 2 := by
    rw [add_sq, sq_sqrt]
    · ring
    · simp [hd] at hx
      apply sub_nonneg_of_le hx.1
  have h₂ {x : ℝ} (hx : x ∈ domain) : x - 4 * √(x - 4) = (2 - √(x - 4)) ^ 2 := by
    rw [sub_sq, sq_sqrt]
    · ring
    · simp [hd] at hx
      apply sub_nonneg_of_le hx.1

  -- Damit kann man $f(x)$ in der Form
  -- $$ f(x)=|2+\sqrt{x-4}|+|2-\sqrt{x-4}| $$
  have h₃ {x : ℝ} (hx : x ∈ domain) : f x = 2 + √(x - 4) + |2 - √(x - 4)| := by
    simp [hf]
    rw [h₁ hx, h₂ hx]
    rw [sqrt_sq_eq_abs, sqrt_sq_eq_abs]
    rw [abs_of_nonneg]
    positivity
  -- schreiben. Für $4 \leq x \leq 8$ ist $\sqrt{x-4} \leq 2$ (für $x8$ ist $\sqrt{x-4}&gt;2$. Daraus folgt
  -- $$ f(x)=2+\sqrt{x-4}-(2-\sqrt{x-4})=2 \sqrt{x-4}&gt;4 $$
  have h₄ {x : ℝ} (hx : x ∈ domain) : f x ≥ 4 := by
    rw [h₃ hx]
    by_cases h : 2 - √(x - 4) < 0
    · rw [abs_of_neg h]
      rw [neg_sub]
      ring_nf at h ⊢
      apply le_of_lt
      linarith only [h]
    · rw [abs_of_nonneg (le_of_not_lt h)]
      ring_nf
      rfl

  -- Demnach ist $f_{\min }(x)=4$ für alle $x$ mit $4 \leq x \leq 8$.
  ext x
  constructor <;> intro h
  · simp at h ⊢
    obtain ⟨hx, hm⟩ := h
    apply isMinOn_iff.mp at hm
    have : f x = 4 := by
      apply le_antisymm ?_ (h₄ hx)
      have : 4 ∈ domain := by simp [hd]
      apply hm 4 at this
      apply le_of_le_of_eq this
      simp [hf]
      rw [show (4 : ℝ) = 2 ^ 2 by ring]
      rw [sqrt_sq_eq_abs]
      norm_num
    have : 2 - √(x - 4) ≥ 0 := by
      by_contra h
      push_neg at h
      rw [h₃ hx] at this
      rw [abs_of_neg h] at this
      ring_nf at h this
      linarith only [h, this]
    simp at this
    apply sqrt_le_iff.mp at this
    norm_num at this
    simp [hd] at hx
    exact ⟨hx.1, this⟩
  · simp
    have hx : x ∈ domain := by
      simp [hd, h.1]
      constructor
      · apply add_nonneg
        · linarith only [h.1]
        · positivity
      · apply pow_le_pow_iff_left₀ (n := 2) ?_ ?_ (by positivity) |>.mp
        · rw [mul_pow, sq_sqrt]
          · apply sub_nonneg.mp
            trans (x - 8) ^ 2
            · positivity
            · apply le_of_eq
              ring
          · apply sub_nonneg_of_le h.1
        · positivity
        · linarith only [h.1]
    use hx
    refine isMinOn_iff.mpr ?_
    intro y hy
    apply le_trans ?_ (h₄ hy)
    apply le_of_eq
    simp at h
    have hx : x ∈ domain := by
      simp [hd, h.1]
      constructor
      · apply add_nonneg
        · linarith only [h.1]
        · positivity
      · apply pow_le_pow_iff_left₀ (n := 2) ?_ ?_ (by positivity) |>.mp
        · rw [mul_pow, sq_sqrt]
          · apply sub_nonneg.mp
            trans (x - 8) ^ 2
            · positivity
            · apply le_of_eq
              ring
          · apply sub_nonneg_of_le h.1
        · positivity
        · linarith only [h.1]
    rw [h₃ hx]
    have : 2 - √(x - 4) ≥ 0 := by
      simp
      apply sqrt_le_iff.mpr
      norm_num
      exact h.2
    rw [abs_of_nonneg this]
    ring
