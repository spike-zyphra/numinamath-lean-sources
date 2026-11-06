import Mathlib
open Real

theorem algebra_9107 {f : ℝ → ℝ} (hf : f = fun x => x / exp x) :
    IsGreatest (Set.range f) (1 / exp 1) := by
  have h1 : ∀ x, f x = x / exp x := by
    intro x
    rw [hf]

  -- Show that $1 / exp 1$ is in the range of $f$.
  have h2 : (1 / exp 1) ∈ Set.range f := by
    use 1
    rw [h1]
    all_goals norm_num

  -- Show that $1 / exp 1$ is the greatest value in the range of $f$.
  have h3 : ∀ y ∈ Set.range f, y ≤ 1 / exp 1 := by
    intro y hy
    rcases hy with ⟨x, hx⟩
    have hfx : f x = x / exp x := by
      rw [hf]
    rw [hfx] at hx
    have h4 : x / exp x ≤ 1 / exp 1 := by
      have h5 : exp x ≥ exp 1 * x := by
        have h7 : exp x ≥ exp 1 * x := by
          have h9 : exp x = exp 1 * exp (x - 1 : ℝ) := by
            calc
              exp x = exp (1 + (x - 1 : ℝ)) := by
                ring_nf
              _ = exp (1 : ℝ) * exp (x - 1 : ℝ) := by
                rw [Real.exp_add]
              _ = exp 1 * exp (x - 1 : ℝ) := by
                norm_num
          have h10 : exp (x - 1 : ℝ) ≥ (x) := by
            have h4 : exp (x - 1 : ℝ) ≥ (1 + (x - 1 : ℝ)) := by
              linarith [Real.add_one_le_exp (x - 1 : ℝ), Real.exp_pos (x - 1 : ℝ)]
            have h8 : 1 + (x - 1) = x := by
              ring
            rw [h8] at h4
            linarith
          rw [h9]
          have h12 : exp 1 > 0 := by
            positivity
          nlinarith
        linarith
      have h2 : exp x > 0 := Real.exp_pos x
      have h3 : exp (1 : ℝ) > 0 := Real.exp_pos (1 : ℝ)
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    linarith [hx, h4]

  constructor
  · -- Show that $1 / exp 1$ is in the range of $f$.
    exact h2
  · -- Show that any value in the range of $f$ is less than or equal to $1 / exp 1$.
    intro y hy
    exact h3 y hy