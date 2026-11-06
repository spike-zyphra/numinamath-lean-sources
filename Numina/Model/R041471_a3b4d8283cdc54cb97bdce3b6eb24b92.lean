import Mathlib

theorem algebra_290344 :
  {d : ℝ | d > 0 ∧ d^2 - 500 * d + 57600 = 0} = {320, 180} := by
  ext d
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume d > 0 ∧ d ^ 2 - 500 * d + 57600 = 0, prove d ∈ {320, 180}
    rintro ⟨hd, heq⟩
    have h1 : d ^ 2 - 500 * d + 57600 = 0 := heq
    have h2 : (d - 320) * (d - 180) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- $d - 320 = 0$, so $d = 320$
      left
      linarith
    · -- $d - 180 = 0$, so $d = 180$
      right
      linarith
  · -- Assume d ∈ {320, 180}, prove d > 0 ∧ d ^ 2 - 500 * d + 57600 = 0
    rintro (rfl | rfl)
    · -- $d = 320$
      constructor
      · norm_num
      · norm_num
    · -- $d = 180$
      constructor
      · norm_num
      · norm_num