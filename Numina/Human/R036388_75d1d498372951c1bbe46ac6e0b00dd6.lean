import Mathlib

/- Let $a$ and $b$ be integer solutions to $17 a+6 b=13$. What is the smallest possible positive value for $a-b$ ?-/
theorem number_theory_608165 :
    IsLeast {n : ℤ | 0 < n ∧ ∃ a b, 17 * a + 6 * b = 13 ∧ n = a - b} 17 := by
  -- Break the goal into two parts.
  simp [IsLeast, lowerBounds]
  refine ⟨?_, ?_⟩
  . -- Show that this value (a - b = 17) is indeed possible.
    use 5, -12
    norm_num
  . -- Show that 17 is the least possible positive value.
    intro n hn a b h₀ h₁
    -- Rewrite h₀ to get that 17(a - b) + 23b = 13.
    replace h₀ : 17 * (a - b) + 23 * b = 13 := by
      linarith only [h₀]
    -- Multiply by 19 and then modulo 23 on both sides.
    replace h₀ := congr_arg (19 * · % 23) h₀
    simp at h₀
    rw [show (17 : ℤ) = 17 % 23 by norm_num] at h₀
    rw [<-Int.ModEq.eq_1] at h₀
    norm_num at h₀
    -- We have (a - b) % 23 = 17.
    rw [show 19 * (17 * (a - b) + 23 * b) = (a - b) + 23 * (14 * (a - b) + 19 * b) by ring] at h₀
    rw [Int.ModEq.eq_1, Int.add_emod] at h₀
    norm_num at h₀
    omega

