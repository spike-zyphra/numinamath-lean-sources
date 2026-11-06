import Mathlib

theorem algebra_303673 (a b c : ℝ) (ha : a < 0) (hvertex : ∃ x y, x = -b / (2 * a) ∧ y = c - b ^ 2 / (4 * a) ∧ x < 0 ∧ y > 0)
    (h1 : a + b + c = 0) (h2 : c = 2) :
    -2 < a ∧ a < 0 := by
  rcases hvertex with ⟨x, y, hx_eq, hy_eq, hx_lt_0, hy_gt_0⟩
  have hb : b = -a - 2 := by
    linarith [h1, h2]
  have h3 : x = (a + 2) / (2 * a) := by
    rw [hx_eq]
    rw [hb]
    field_simp [(show a ≠ 0 by linarith)]
    <;> ring_nf <;> field_simp <;> ring_nf
    <;> nlinarith
  have h4 : (a + 2) / (2 * a) < 0 := by
    rw [←h3]
    exact hx_lt_0
  have h5 : -2 < a := by
    apply (div_neg_iff).mp at h4
    cases h4 with
    | inl h =>
      nlinarith
    | inr h =>
      nlinarith
  have h6 : a < 0 := by linarith
  constructor
  · linarith
  · linarith