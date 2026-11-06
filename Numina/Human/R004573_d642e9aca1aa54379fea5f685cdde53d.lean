import Mathlib

theorem algebra_285332 {x y z : ℝ} (hx : x = 1) (hxy : |x - y| = x) (hyz : |y - z| = y)
    (hzx : |z - x| = z) : y = 0 ∧ z = 0 := by
  rw [hx] at hxy hzx
  cases eq_or_eq_neg_of_abs_eq hxy with
  | inl h1 =>
    have hy : y = 0 := by linarith
    have hz : z = 0 := by
      rw [hy] at hyz
      cases eq_or_eq_neg_of_abs_eq hyz with
      | inl h => linarith
      | inr h => linarith
    exact ⟨hy, hz⟩
  | inr h2 =>
    have hy : y = 2 := by linarith
    have hz : z = 0 ∨ z = 4 := by
      rw [hy] at hyz
      cases eq_or_eq_neg_of_abs_eq hyz with
      | inl h => left; linarith
      | inr h => right; linarith
    cases hz with
    | inl hz0 =>
      rw [hz0] at hzx
      norm_num at hzx
    | inr hz4 =>
      rw [hz4] at hzx
      norm_num at hzx