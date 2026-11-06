import Mathlib
open Real
theorem algebra_608829 : IsGreatest {S : ℝ | ∃ x y : ℝ, ∃ f : ℝ → ℝ → ℝ, (∀ a b : ℝ, f a b = sin a * cos b) ∧ f x y - f y x = 1 ∧ S = f x y + f y x} 1:= by
  constructor
  · -- First, we will show that 1 can be achieved.
    use Real.pi / 2, 0, fun a b => sin a * cos b
    constructor
    · -- Show that it satisfies the condition (star operation definition)
      intro a b
      rfl
    constructor
    · -- Show that it satisfies the condition f(x,y) - f(y,x) = 1
      have h1 : sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
      have h2 : cos (0 : ℝ) = 1 := by
        simp
      simp [h1, h2]
    · -- Show that 1 = f(x,y) + f(y,x)
      have h1 : sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
      have h2 : cos (0 : ℝ) = 1 := by
        simp
      have h3 : sin (0 : ℝ) = 0 := by
        simp
      have h4 : cos (Real.pi / 2) = 0 := by
        have h4 : cos (Real.pi / 2) = 0 := by
          exact cos_pi_div_two
        exact h4
      simp [h1, h2, h3, h4]
  · -- Now, we have to show that 1 is greatest in the set
    intro S hS
    rcases hS with ⟨x, y, f, hf, h_eq, hS_eq⟩
    have h1 : f x y = sin x * cos y := by
      apply hf
    have h2 : f y x = sin y * cos x := by
      apply hf
    rw [h1, h2] at h_eq
    rw [h1, h2] at hS_eq
    -- We need to show that S ≤ 1
    have h3 : sin x * cos y - (sin y * cos x) = 1 := by
      linarith
    -- Show that S = sin(x)cos(y) + cos(x)sin(y) = sin(x+y) ≤ 1
    have h4 : sin x * cos y + sin y * cos x ≤ 1 := by
      have h6 : (sin x * cos y + sin y * cos x) ^ 2 + (cos x * cos y - sin x * sin y) ^ 2 = 1 := by
        have h7 : sin (x + y) = sin x * cos y + cos x * sin y := by
          rw [sin_add]
        have h8 : cos (x + y) = cos x * cos y - sin x * sin y := by
          rw [cos_add]
        have h9 : (sin (x + y)) ^ 2 + (cos (x + y)) ^ 2 = 1 := by
          have h10 : sin (x + y) ^ 2 + cos (x + y) ^ 2 = 1 := by
            exact Real.sin_sq_add_cos_sq (x + y)
          linarith [h10]
        rw [h7] at *
        rw [h8] at *
        linarith [h9]
      nlinarith [sq_nonneg (sin x - sin y), sq_nonneg (cos x - cos y), Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y, sq_nonneg (sin x * (cos x - cos y)), sq_nonneg (sin y * (cos x - cos y)), sq_nonneg ((sin x - sin y) * cos x), sq_nonneg ((sin x - sin y) * cos y)]
    linarith [hS_eq, h4]