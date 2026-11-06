import Mathlib

theorem algebra_1413 : {n : ℕ | n > 0 ∧ 3^2 + 4^2 + 12^2 = n^2} = {13} := by
  ext n
  simp
  constructor
  · rintro ⟨h₁, h₂⟩
    rw [Eq.comm, show 169 = 13^2 by rfl] at h₂
    have h₃ : (n : ℝ)^2 = 13^2 := by norm_cast
    rw [sq_eq_sq_iff_eq_or_eq_neg] at h₃
    norm_cast at h₃
    norm_num at h₃
    assumption
  · intro hn
    rw [hn]
    norm_num
