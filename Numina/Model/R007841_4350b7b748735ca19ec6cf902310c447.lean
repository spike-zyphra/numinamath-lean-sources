import Mathlib

theorem algebra_13726 {l w nl nw : ℝ} (hl : 0 < l ∧ 0 < nl) (hw : 0 < w ∧ 0 < nw)
    (h : nl = 1.2 * l ∧ nw = 1.1 * w) :
    (nl * nw - l * w) / (l * w) = 0.32 := by 
  rcases h with ⟨h1, h2⟩
  have h3 : 0 < l := hl.1
  have h4 : 0 < w := hw.1
  have eq1 : nl * nw = 1.32 * (l * w) := by
    rw [h1, h2]
    ring_nf 
    <;> simp [mul_add, mul_assoc, mul_comm, mul_left_comm]
    <;> ring
  have eq2 : (nl * nw - l * w) = 0.32 * (l * w) := by
    linarith [eq1]
    <;> ring_nf <;> linarith
  have h5 : l * w ≠ 0 := mul_ne_zero (ne_of_gt h3) (ne_of_gt h4)
  rw [eq2]
  field_simp [h5]
  <;> ring_nf <;> field_simp [h5] <;> ring