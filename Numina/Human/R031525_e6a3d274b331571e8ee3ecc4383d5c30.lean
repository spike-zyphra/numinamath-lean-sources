import Mathlib

/-
Show that the fourth power of every odd integer is of the form $16k + 1$ for some integer $k$.
-/
theorem number_theory_4986
    (n : ℤ)
    (h : Odd n) :
    ∃ k, n ^ 4 = 16 * k + 1 := by
  -- n = 2 * m + 1
  obtain ⟨m, hm⟩ := h
  -- m * (1 + 3 * m) is even
  obtain ⟨k, hk⟩ : Even (m * (1 + 3 * m)) := by
    refine Int.even_mul.mpr ?_
    rcases Int.even_or_odd m with he | ⟨p, hp⟩
    . left; exact he
    . right
      rw [show 1 + 3 * m = 2 * (2 + p * 3) by rw [hp]; ring]
      apply even_two_mul
  use k + 2 * m ^ 3 + m ^ 4
  calc n ^ 4
    _ = 1 + 8 * (m * (1 + 3 * m)) + 32 * m ^ 3 + 16 * m ^ 4 := by
      rw [hm]
      ring
    _ = 16 * (k + 2 * m ^ 3 + m ^ 4) + 1 := by
      rw [hk]
      ring
