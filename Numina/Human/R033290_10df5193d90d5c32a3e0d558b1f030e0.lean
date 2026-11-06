import Mathlib

/-
  The roots of the equation $x^{2}+2x+3=0$ in the complex number field are ______.
-/
theorem algebra_9015 (x : ℂ) :
    x ^ 2 + 2 * x + 3 = 0 ↔ x = -1 + √ 2 * .I ∨ x = -1 - √ 2 * .I := by
  constructor
  · intro hx
    -- write x as a + b * i, substitute into the equation
    have hc : x = x.re + x.im * .I := by exact Eq.symm (Complex.re_add_im x)
    rw [hc] at hx
    rw [add_sq, mul_add] at hx
    rw [mul_pow] at hx
    norm_num at hx
    apply Complex.ext_iff.mp at hx
    simp at hx
    obtain ⟨h1, h2⟩ := hx
    norm_cast at h1 h2
    -- obtain that a = -1 or b = 0
    have : 2 * (x.re + 1) * x.im = 0 := by rw [<-h2]; ring
    simp at this
    rcases this with h | h
    · -- if a = -1, then b ^ 2 = 2
      have hre : x.re = -1 := by linear_combination h
      rw [hre] at h1
      have : x.im ^ 2 = 2 := by linear_combination -1 * h1
      -- b = √ 2 ∨ √ -2 → done
      have : x.im = √ 2 ∨ x.im = -√ 2 := by
        apply mul_self_eq_mul_self_iff.mp
        ring_nf
        rw [this]
        norm_num
      rcases this with h | h <;> (rw [h, hre] at hc; simp [hc])
      apply Or.inr
      ring
    · -- if b = 0, then (a + 1) ^ 2 < 0, contradiction
      simp [h] at h1
      have : (x.re + 1) ^ 2 = -2 := by linear_combination h1
      have : (x.re + 1) ^ 2 ≥ 0 := by exact sq_nonneg (x.re + 1)
      linarith
  · -- verify the answer
    intro hx
    rcases hx with h | h
    all_goals
    simp [h]
    ring_nf
    norm_cast
    norm_num
