import Mathlib

/-There are thirty-five red, yellow, orange, and white marbles in a bag. If half the number of red marbles equals two less than the number of yellow marbles, equals a third the number of orange marbles, and equals a third of three more than the number of white marbles, how many red marbles are there?-/
theorem algebra_21278 (r y o w : ℕ) (h₀ : r + y + o + w = 35)
    (h₁ : (r : ℝ) / 2 = y - 2) (h₂ : (r : ℝ) / 2 = o / 3) (h₃ : (r : ℝ) / 2 = (w + 3 : ℝ) / 3) :
    r = 8 := by
  field_simp at h₁ h₂ h₃
  -- show that r = 2y - 4
  replace h₁ : (r : ℝ) = 2 * y - 4 := by ring_nf at h₁ ⊢; exact h₁
  -- show that o = 3y - 6
  replace h₂ : (o : ℝ) = 3 * y - 6 := by 
    rw [h₁] at h₂
    calc
      (o : ℝ) = (2 * (o : ℝ)) / 2 := by field_simp
      _ = ((2 * (y : ℝ) - 4) * 3) / 2 := by rw [h₂]; field_simp
      _ = 3 * (y : ℝ) - 6 := by field_simp; ring_nf
  -- show that w = 3y - 9
  replace h₃ : (w : ℝ) = 3 * y - 9 := by
    rw [h₁] at h₃
    calc
      (w : ℝ) = ((w : ℝ) + 3) * 2 / 2 - 3 := by ring_nf
      _ = (2 * (y : ℝ) - 4) * 3 / 2 - 3 := by rw [h₃]
      _ = 3 * (y : ℝ) - 9 := by ring_nf
  -- substitute all above to h₀
  replace h₀ : (r : ℝ) + y + o + w = 35 := by norm_cast
  rw [h₁, h₂, h₃] at h₀
  ring_nf at h₀
  -- show that y = 6
  have hy : (y : ℝ) = 6 := by linarith only [h₀]
  -- show that r = 8
  rw [hy] at h₁
  ring_nf at h₁
  norm_cast at h₁