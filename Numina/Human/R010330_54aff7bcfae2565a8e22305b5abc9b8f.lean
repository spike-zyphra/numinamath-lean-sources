import Mathlib

/-At which point do the lines $s=9-2t$ and $t=3s+1$ intersect? Give your answer as an ordered pair in the form $(s, t).$-/
theorem algebra_21541 :
    {(s, t) : ℝ × ℝ | s = 9 - 2 * t ∧ t = 3 * s + 1} = {(1, 4)} := by
  ext x
  simp
  -- divide into two parts
  apply Iff.intro <;> intro h
  -- show that x is (1, 4)
  . obtain ⟨hs, ht⟩ := h
    -- show that s = 9 - 2(3s + 1)
    rw [ht] at hs
    -- show that s = 1 and t = 4
    have hx1 : x.1 = 1 := by linarith only [hs]
    have hx2 : x.2 = 4 := by rw [hx1] at ht; linarith only [ht]
    calc
      x = (x.1, x.2) := by rfl
      _ = (1, 4) := by rw [hx1, hx2]
  -- show that x is in {(1, 4)}
  . obtain ⟨h1, h2⟩ := h
    norm_num