import Mathlib
open Real Set
open scoped BigOperators

/- Given the function $f\left(x\right)=\sin ^{2}x-\cos ^{2}x-2\sqrt{3}\sin x \cos x\left(x\in R\right)$.
(Ⅰ) Find the value of $f(\frac{2π}{3})$.
(Ⅱ) Find the minimum positive period and the interval of monotonic increase of $f\left(x\right)$. -/
theorem algebra_9439 {f : ℝ → ℝ} (hf : f = λ x => sin x ^ 2 - cos x ^ 2 - 2 * sqrt 3 * sin x * cos x) :
    f (2 * π / 3) = 2 ∧
    IsLeast {T | 0 < T ∧ f = λ x => f (x + T)} π ∧
    ∀ k : ℤ, MonotoneOn f (Icc (k * π + π / 6) (k * π + 2 * π / 3)) := by
  -- Simply the expression of f.
  have lm : sin (π * (7 / 6)) = -1 / 2 ∧ cos (π * (7 / 6)) = -√3 / 2 := by
    refine ⟨?_, ?_⟩
    all_goals
      rw [(by ring : π * (7 / 6) = π - -(π / 6))]
      try rw [sin_pi_sub, sin_neg]
      try rw [cos_pi_sub, cos_neg]
      field_simp
  have f_eq (x : ℝ) : f x = 2 * sin (2 * x + π * (7 / 6)) := by
    calc
      f x = sin x ^ 2 - cos x ^ 2 - 2 * √3 * sin x * cos x := by tauto
      _ = -(cos x ^ 2 - sin x ^ 2) - √3 * (2 * sin x * cos x) := by linarith
      _ = -cos (2 * x) - √3 * sin (2 * x) := by rw [cos_two_mul', sin_two_mul]
      _ = 2 * sin (2 * x + π * (7 / 6)) := by simp [sin_add, lm]; ring_nf
  refine ⟨?_, ?_, ?_⟩
  . -- Evaluate the value of f (2π / 3).
    simp [hf]
    rw [(by ring_nf : 2 * π / 3 = π - π / 3), sin_pi_sub, cos_pi_sub, sin_pi_div_three, cos_pi_div_three]
    field_simp
    rw [mul_assoc, mul_self_sqrt]
    norm_num
    norm_num
  . -- Find the minimum positive period.
    simp [IsLeast, lowerBounds]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    . -- 0 < π.
      exact pi_pos
    . -- π is a period.
      simp [hf]
    . -- T ≥ π if f(x) = f(x + T) for all x and positive T > 0.
      intro T T_pos T_period
      replace T_period : ∀ x, f x = f (x + T) := by
        intro x
        tauto
      -- Choose x such that 2 * x + π * (7 / 6) = π / 2.
      specialize T_period (-π / 3)
      conv at T_period =>
        simp [f_eq, f_eq]
        ring_nf
        rw [(by ring_nf : π * (1 / 2) = π / 2), sin_pi_div_two]
      symm at T_period
      rw [sin_eq_one_iff] at T_period -- From equation of the form 1 = sin x, we can obtain x = 2kπ.
      obtain ⟨k, hk⟩ := T_period
      replace hk : T = k * π := by linarith
      rw [hk] at T_pos ⊢
      replace T_pos : (0 : ℝ) < k := by nlinarith [pi_pos]
      replace T_pos : 0 < k := Int.cast_pos.1 T_pos
      replace T_pos : (1 : ℝ) ≤ k := Int.cast_one_le_of_pos T_pos
      nlinarith [pi_pos]
  . -- Prove the interval of monotonic increase of f.
    intro k x hx y hy hxy -- Rephrase the goal to f x ≤ f y.
    simp [Icc] at hx hy
    rw [f_eq, f_eq]
    simp
    obtain ⟨hx₁, _⟩ := hx
    obtain ⟨_, hy₂⟩ := hy
    have g : sin (2 * x + π * (7 / 6) + (-k - 1 : ℤ) * (2 * π)) ≤ sin (2 * y + π * (7 / 6) + (-k - 1 : ℤ) * (2 * π)) := by
      apply sin_le_sin_of_le_of_le_pi_div_two
      repeat
        simp
        linarith
    rw [sin_add_int_mul_two_pi, sin_add_int_mul_two_pi] at g
    exact g
