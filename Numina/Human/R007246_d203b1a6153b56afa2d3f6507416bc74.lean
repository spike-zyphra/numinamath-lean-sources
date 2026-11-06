import Mathlib

/- Find the least positive integer $x$ that satisfies $x+4609 \equiv 2104 \pmod{12}$. -/
theorem number_theory_11171 : IsLeast {x : ℕ | 0 < x ∧ (x + 4609) % 12 = 2104 % 12} 3 := by
  refine ⟨by decide, ?_⟩
  intro y h
  norm_num at h
  omega