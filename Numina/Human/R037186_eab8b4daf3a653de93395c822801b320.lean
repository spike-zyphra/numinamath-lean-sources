import Mathlib

theorem number_theory_125666 :
    IsLeast {p : ℕ | p.Prime ∧ IsSquare (5 * p^2 + p^3)} 11 := by
  constructor
  · norm_num
    native_decide
  · intro n
    rintro ⟨hn₁, hn₂⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn₁
                     <;> revert hn₂
                     <;> native_decide
