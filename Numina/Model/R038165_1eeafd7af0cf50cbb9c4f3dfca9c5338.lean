import Mathlib

theorem algebra_10872 (A B : ℝ × ℝ → Prop)
    (hA : A = fun (x,y) => x^2 - 9*x +25 = y)
    (hB : B = fun (x,y) => x - 8 = y) :
    IsLeast {k | ∃ p q, A p ∧ B q ∧ k = √((p.1-q.1)^2+(p.2-q.2)^2)} (4 * Real.sqrt 2) := by
  constructor
  · -- Show 4 * Real.sqrt 2 is indeed in the set.
    use (5, 5)
    use (9, 1)
    constructor
    · -- Show (5, 5) is on the parabola.
      rw [hA]
      norm_num
    constructor
    · -- Show (9, 1) is on the line.
      rw [hB]
      norm_num
    · -- Check that 4 * Real.sqrt 2 equals the distance.
      have h1 : Real.sqrt ((5 - 9 : ℝ) ^ 2 + (5 - (1 : ℝ)) ^ 2) = 4 * Real.sqrt 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      rw [h1]
      all_goals norm_num
  · -- Show 4 * Real.sqrt 2 is minimal.
    intro k hk
    rcases hk with ⟨p, q, hp, hq, hk⟩
    rw [hA] at hp
    rw [hB] at hq
    rcases p with ⟨x, y⟩
    rcases q with ⟨t, s⟩
    simp at hp hq
    have h1 : (x - t) ^ 2 + (y - s) ^ 2 ≥ 32 := by
      have h2 : s = t - 8 := by linarith
      rw [h2]
      have h3 : y = x ^ 2 - 9 * x + 25 := by linarith
      rw [h3]
      nlinarith [sq_nonneg (x - 5), sq_nonneg (t - 9), sq_nonneg (x - 5), sq_nonneg (t - 9), sq_nonneg (x - t + 4), sq_nonneg (x + t - 10), sq_nonneg ((x - 5) - (t - 9)), sq_nonneg (x - 5 + (t - 9)), sq_nonneg (x^2 - 10 * x + 25), sq_nonneg (t^2 - 18 * t + 81)]
    have h3 : Real.sqrt ((x - t) ^ 2 + (y - s) ^ 2) ≥ Real.sqrt (32) := Real.sqrt_le_sqrt (by linarith [h1])
    have h4 : Real.sqrt (32) = 4 * Real.sqrt 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    have h5 : Real.sqrt ((x - t) ^ 2 + (y - s) ^ 2) = Real.sqrt ((x - t) ^ 2 + (y - s) ^ 2) := by rfl
    linarith [h3, h4, Real.sqrt_nonneg ((x - t) ^ 2 + (y - s) ^ 2), Real.sqrt_nonneg (32), Real.sqrt_nonneg 2, Real.sqrt_nonneg 2]