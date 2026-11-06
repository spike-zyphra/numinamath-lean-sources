import Mathlib

theorem number_theory_293263 (n : ℤ) :
    Set.Finite {(a, b) : ℤ × ℤ | a^2 + a * b + b^2 = n} := by
  have : {(a, b) : ℤ × ℤ | a^2 + a * b + b^2 = n} = Finset.filter (fun s : ℤ × ℤ => s.1^2 + s.1 * s.2 + s.2^2 = n) (Finset.Icc (-2 * n) (2 * n) ×ˢ Finset.Icc (-2 * n) (2 * n)) := by
    ext ⟨a, b⟩
    simp
    intro h
    have h2 : a^2 + a * b + b^2 = n := h
    have h4 : a ≥ -2 * n := by
      nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (b + n), sq_nonneg (a - n)]
    have h5 : a ≤ 2 * n := by
      nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (b + n), sq_nonneg (a - n)]
    have h6 : b ≥ -2 * n := by
      nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (a + n), sq_nonneg (b - n)]
    have h7 : b ≤ 2 * n := by
      nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (a + n), sq_nonneg (b - n)]
    omega
  rw [this]
  apply Set.toFinite