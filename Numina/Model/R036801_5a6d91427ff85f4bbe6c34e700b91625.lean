import Mathlib

open Real

theorem algebra_172443 {B E : ℝ} (hB : B > 0) (hE : E > B) 
    (a_def : a = 100 * (E/B - 1)) 
    (f_def : f = 100 * (1 - B/E)) :
    -- 命题1: 从a可以推导出f，且与B无关
    (∀ a, ∃ f, f = 100 * a / (a + 100)) ∧
    -- 命题2: a和f的差等于它们乘积的百分之一
    (a - f = (a * f)/100) := by
  constructor
  · -- First part: prove the conversion from a to f.
    intro a 
    refine ⟨100 * a / (a + 100), by simp⟩ 
  · -- Second part: prove the difference.
    rw [a_def, f_def]
    have h1 : E / B > 1 := by
      have hEB : E > B := by linarith
      have hB' : B > 0 := hB
      have h2 : E / B > 1 := by
        apply (lt_div_iff₀ (by linarith)).mpr
        linarith
      linarith
    have h4 : B ≠ 0 := by linarith 
    have h3 : E ≠ 0 := by linarith 
    field_simp [h3, h4]
    <;> ring