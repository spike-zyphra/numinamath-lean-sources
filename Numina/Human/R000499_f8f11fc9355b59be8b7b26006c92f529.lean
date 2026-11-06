import Mathlib

/-Find the positive real number $x$ such that $\lfloor x \rfloor \cdot x = 70$. Express $x$ as a decimal.-/
theorem algebra_11454 {x : ℝ} (hx : x > 0) (h : ⌊x⌋ * x = 70) : x = 8.75 := by
  have h1 : x < ⌊x⌋ + 1 := Int.lt_floor_add_one x
  have h2 : ⌊x⌋ ≤ x := Int.floor_le x
  -- Knowing that $\lfloor x \rfloor \leq x < \lfloor x \rfloor + 1,$
  -- we see that $\lfloor x \rfloor$ must be $8,$ since $8 \cdot 8 \leq 70 < 9 \cdot 9.$
  have : ⌊x⌋ = 8 := by
    rcases lt_trichotomy ⌊x⌋ 8 with h3 | h3 | h3
    · have : ⌊x⌋ * x < 70 := calc
          _ < (7 : ℝ) * 9 := by
            have : x < 9 := by
              norm_cast at h1
              exact h1.trans (by norm_cast; linarith)
            have : ⌊x⌋ ≤ (7 :ℝ) := by norm_cast; linarith
            apply mul_lt_mul' this <;> linarith
          _ < 70 := by linarith
      linarith
    · tauto
    · have : 70 < ⌊x⌋ * x := calc
        _ < (9 : ℝ) * 9 := by linarith
        _ ≤ _ := by
          have tmp : (9 : ℝ) ≤ ⌊x⌋ := by norm_cast
          have : 9 ≤ x := tmp.trans h2
          apply mul_le_mul <;> linarith
      linarith
  -- Now we see that $\lfloor x \rfloor \cdot x = 8x = 70,$ so $x = \frac{70}{8} = \boxed{8.75}.$
  rw [this] at h
  apply_fun (· / 8) at h
  norm_num at h
  rw [h]
  ring
