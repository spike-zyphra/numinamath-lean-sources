import Mathlib

theorem algebra_152006 {a b c : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = a * x ^ 2 + b * x + c)
    (h0 : f 0 = 0) (h1 : ∀ x, f (x + 1) = f x + x + 1) :
    ∀ x, f x = x ^ 2 / 2 + x / 2 := by
  have hc : c = 0 := by 
    rw [hf 0] at h0
    linarith
  
  have h_eq1 := h1 0
  simp [hf, hc] at h_eq1
  
  have eq1 : a + b = 1 := by 
    linarith [h_eq1]

  have h_eq2 := h1 1
  simp [hf, hc] at h_eq2
  
  have eq2 : 3 * a + b = 2 := by
    linarith [h_eq2]

  have ha : a = 1 / 2 := by
    linarith [eq1, eq2]

  have hb : b = 1 / 2 := by
    linarith [eq1, ha]

  intro x
  rw [hf x]
  rw [ha, hb, hc]
  ring_nf