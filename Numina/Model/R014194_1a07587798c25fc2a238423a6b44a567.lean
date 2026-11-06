import Mathlib

theorem number_theory_76937 (N : ℕ) (a b c : ℤ) (ha : 3 ∣ a) (hb : 3 ∣ b) (hc : 3 ∣ c)
    (h : N = a^2 + b^2 + c^2) :
    ∃ x y z, 3 ∣ x ∨ 3 ∣ y ∨ 3 ∣ z ∧ N = x^2 + y^2 + z^2 := by 
  refine' ⟨0, a.natAbs, b.natAbs, Or.inl (by simp)⟩
  all_goals
    simp [h, sq_abs, Int.ofNat, abs_nonneg] at *
    <;> norm_num at *
    <;> ring_nf at *
    <;> nlinarith [sq_nonneg (a: ℤ), sq_nonneg (b: ℤ), sq_nonneg (c: ℤ), sq_nonneg (c: ℤ), sq_nonneg (a - a: ℤ), sq_nonneg (b - b: ℤ), sq_nonneg (c - c: ℤ)]