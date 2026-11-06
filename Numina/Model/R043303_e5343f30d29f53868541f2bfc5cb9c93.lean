import Mathlib

open Filter Function Real Topology


lemma lemma_1 {f : ℝ → ℝ} (hf : ∀ x, f x = abs x) :
    DifferentiableOn ℝ f (Set.Ioi 0) := by
  rw [show f = abs by funext x; exact hf x]
  have h1 : DifferentiableOn ℝ (fun x : ℝ => abs x) (Set.Ioi (0 : ℝ)) := by
    have h_eq : ∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → abs x = x := by
      intro x hx
      have hx_pos : 0 < x := by
        simpa using hx
      rw [abs_of_pos hx_pos]
    apply DifferentiableOn.congr
    ·
      apply differentiableOn_id
    ·
      intro x hx
      apply h_eq x hx
  exact h1


theorem calculus_137623 {f : ℝ → ℝ} (hf : ∀ x, f x = abs x) :
    DifferentiableOn ℝ f (Set.Iio 0) ∧ DifferentiableOn ℝ f (Set.Ioi 0) := by 
  constructor
  · -- Show differentiable on (-∞, 0)
    rw [show f = abs by funext x; exact hf x]
    have h2 : DifferentiableOn ℝ (fun x : ℝ => abs x) (Set.Iio (0 : ℝ)) := by
      have h_eq2 : ∀ x : ℝ, x ∈ Set.Iio (0 : ℝ) → abs x = -x := by
        intro x hx
        have hx_neg : x < (0 : ℝ) := by
          simpa using hx
        rw [abs_of_neg hx_neg]
      apply DifferentiableOn.congr
      · -- The function `g(x) = -x` is differentiable
        apply DifferentiableOn.neg
        apply differentiableOn_id
      · -- Show that for all x in Iio 0, abs x = -x
        intro x hx
        apply h_eq2 x hx
    exact h2
  · -- Show differentiable on (0, ∞)
    apply lemma_1 hf