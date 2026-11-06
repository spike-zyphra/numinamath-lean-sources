import Mathlib

/- What is the smallest positive multiple of $23$ that is $4$ more than a multiple of $89$? -/
theorem number_theory_14623 :
    IsLeast {x | 0 < x ∧ 23 ∣ x ∧ ∃ k, x = 89 * k + 4} 805 := by
  refine' ⟨⟨by decide, by decide, 9, by decide⟩, fun x ⟨_, _, k, hk⟩ => _⟩
  rw [hk]
  norm_num
  omega