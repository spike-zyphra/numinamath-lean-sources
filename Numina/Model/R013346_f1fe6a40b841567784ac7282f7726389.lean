import Mathlib

theorem algebra_263453 (a b c d : ℕ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : d > 0) (h₄ : a ≠ b) (h₅ : a ≠ c) (h₆ : a ≠ d) (h₇ : b ≠ c) (h₈ : b ≠ d)
    (h₉ : c ≠ d) (h₁₀ : a = 2 * b) (h₁₁ : b = 2 * c) (h₁₂ : c = 2 * d) :
    a / (a + b + c + d : ℚ) = 8 / 15 := by 
  have ha : a = 8 * d := by 
    linarith [h₁₀, h₁₁, h₁₂]
  have hb : b = 4 * d := by 
    linarith [h₁₁, h₁₂]
  have hc : c = 2 * d := by 
    linarith [h₁₂]
  have ha' : (a : ℚ) = 8 * (d : ℚ) := by 
    exact_mod_cast ha
  have hb' : (b : ℚ) = 4 * (d : ℚ) := by 
    exact_mod_cast hb
  have hc' : (c : ℚ) = 2 * (d : ℚ) := by 
    exact_mod_cast hc
  have htotal : (a + b + c + d : ℚ) = 15 * (d : ℚ) := by
    linarith [ha', hb', hc', show (d : ℚ) = (d : ℚ) by rfl]
  rw [htotal]
  rw [ha']
  have h13 : (d : ℚ) ≠ 0 := by 
    have h' : (d : ℚ) > 0 := by exact_mod_cast h₃
    linarith
  field_simp [h13]
  <;> ring_nf
  <;> field_simp [h13]
  <;> ring_nf