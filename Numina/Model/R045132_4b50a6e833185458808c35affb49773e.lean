import Mathlib

theorem algebra_11198 (f : ℝ → ℝ) (hf : ∃ a b c, f = fun x => a * x ^ 2 + b * x + c)
    (h1 : f 2 = 0) (h2 : f 4 = 0) (h3 : f 3 = 6) :
    f = fun x => -6 * x ^ 2 + 36 * x - 48 := by 
  rcases hf with ⟨a, b, c, hf⟩
  have eq1 : a * 2 ^ 2 + b * 2 + c = 0 := by
    rw [hf] at h1
    simpa using h1
  have eq2 : a * 4 ^ 2 + b * 4 + c = 0 := by
    rw [hf] at h2
    simpa using h2
  have eq3 : a * 3 ^ 2 + b * 3 + c = 6 := by
    rw [hf] at h3
    simpa using h3
  have ha : a = -6 := by
    nlinarith
  have hb : b = 36 := by
    nlinarith [ha]
  have hc : c = -48 := by
    nlinarith [ha, hb, eq1]
  funext x
  simp [hf, ha, hb, hc]
  <;> ring_nf