import Mathlib

theorem algebra_12164 : {x : ℝ | x ≠ 0 ∧ (5 * x)^4 = (10 * x)^3} = {8/5} := by
  ext x
  simp
  constructor
  · rintro ⟨hx, h⟩
    ring_nf at h
    have h1 : x ^ 3 * (5 * x - 8) = 0 := by
      linarith
    rw [mul_eq_zero] at h1
    rcases h1 with h2 | h3
    · have h4 : x = 0 := by
        have : x ^ 3 = 0 := by linarith
        simp at this
        exact this
      contradiction
    · linarith
  · intro hx
    rw [hx]
    norm_num
