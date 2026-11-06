import Mathlib

noncomputable def S (a b c: ℝ) :=
  let s:= (a + b + c) / 2
  √(s * (s - a) * (s - b) * (s - c))

/-The altitudes of a triangle are 12,15 and 20. What is the area of the triangle?
Answer: 150.-/

theorem geometry_606364 (a b c h_a h_b h_c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : h_a = 12) (h₂ : h_b = 15) (h₃ : h_c = 20) (h₄ : a / b = h_b / h_a)
    (h₅ : b / c = h_c / h_b) (h₆: S a b c = a * h_a / 2):
    S a b c = 150 := by

    rw [h₆]
    rcases h₀ with ⟨p1, p2, p3⟩
    simp [S] at h₆
    replace h₄: b = 4 / 5 * a := by
        simp [h₂, h₁] at h₄
        field_simp at h₄
        clear *- h₄
        linarith
    simp [h₂, h₃] at h₅
    field_simp at h₅
    replace h₅: c = 3 / 5 * a := by
        linarith
    simp [h₄, h₅, h₁] at h₆
    ring_nf at h₆
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos] at h₆
    ring_nf at h₆
    replace h₆: a = 25 := by
        clear *- h₆ p1
        replace h₆: a ^ 2 * (a - 25) * (a + 25) = 0 := by
            nlinarith
        simp at h₆
        rcases h₆ with p | p
        .
            rcases p with p | p
            .
                simp [p] at p1
            .
                nlinarith
        .
            nlinarith
    rw [h₆, h₁]
    norm_num
    linarith