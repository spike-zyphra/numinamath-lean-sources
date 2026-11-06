import Mathlib

theorem number_theory_624864 : {M : ℕ | 10 < M ∧ M < 100 ∧ IsSquare (M + (M % 10) * 10 + M / 10)}.ncard = 8 := by
  suffices {M : ℕ | 10 < M ∧ M < 100 ∧ IsSquare (M + (M % 10) * 10 + M / 10)} = {29, 38, 47, 56, 65, 74, 83, 92} by
    rw [this]
    norm_num
  ext m
  constructor <;> simp
  · intro hm₁ hm₂ hm₃
    interval_cases m <;>
      norm_num at hm₃ ⊢ <;>
      revert hm₃ <;>
      native_decide
  · rintro (hm | hm | hm | hm | hm | hm | hm | hm) <;>
      rw [hm] <;>
      norm_num <;>
      native_decide
