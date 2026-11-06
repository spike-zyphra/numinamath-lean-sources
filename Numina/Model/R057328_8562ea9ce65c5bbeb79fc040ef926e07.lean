import Mathlib

theorem algebra_143313 {a b c : ℝ} (f : ℝ → ℝ) (hf : f = fun x => a + b * c ^ x)
    (h0 : f 0 = 5) (h1 : f 1 = 14) (h2 : f 2 = 50) :
    f = fun x => 2 + 3 * 4 ^ x := by
  have eq1 : a + b = 5 := by
    rw [hf] at h0
    norm_num at h0
    linarith
  have eq2 : a + b * c = 14 := by
    rw [hf] at h1
    norm_num at h1
    linarith
  have eq3 : a + b * c^2 = 50 := by
    rw [hf] at h2
    norm_num at h2
    linarith
  have h3 : a = 5 - b := by linarith
  rw [h3] at eq2 eq3
  have h4 : b * (c - 1) = 9 := by
    nlinarith
  have h5 : b * (c ^ 2 - 1) = 45 := by
    nlinarith
  have h6 : b * (c - 1) * (c + 1) = 45 := by
    ring_nf at h5 ⊢
    linarith
  rw [show b * (c - 1) = 9 by linarith [h4]] at h6
  have h7 : c + 1 = 5 := by
    nlinarith
  have h8 : c = 4 := by linarith
  have h9 : b = 3 := by
    rw [h8] at h4
    nlinarith
  have h10 : a = 2 := by
    linarith [h9]
  ext x
  simp [hf, h10, h9, h8]
  <;> ring_nf <;> simp_all
  all_goals ring_nf <;> simp_all