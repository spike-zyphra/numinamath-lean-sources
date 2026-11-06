import Mathlib

theorem algebra_309414 {f : ℝ → ℝ} (hf : ∃ a b, f = fun x => x / (a * x + b)) (hb : b > 0)
    (h2 : f 2 = 1) (hunique : ∀ x, f x = x ↔ x = 2) :
    ∀ x, f x = x / (2 * x + 1005 * π) ∧
    (∑ i ∈ Finset.range 2011, (1 / (2 * i + 1005 * π))) = 2011 * (2 + 1005 * π) / (2 * π) := by
  rcases hf with ⟨a, b, h_eq⟩
  have h0 : f 0 = (0 : ℝ) := by
    rw [h_eq]
    norm_num
    all_goals try { linarith }
  have h01 : f 0 = (0 : ℝ) := h0
  have h02 := hunique 0
  have h03 : (f 0 = (0 : ℝ)) ↔ (0 = (2 : ℝ)) := h02
  rw [h01] at h03
  norm_num at h03
  all_goals try { linarith }