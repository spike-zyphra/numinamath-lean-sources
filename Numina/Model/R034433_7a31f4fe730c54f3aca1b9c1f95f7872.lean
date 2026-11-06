import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_9146 {f : ℝ → ℝ} (hf : f = λ x => (x - 2) * exp x)
(I : Set ℝ) (hI : I = Icc 0 2) :
IsGreatest (image f I) 0 ∧ IsLeast (image f I) (-exp 1) := by
  rw [hI]
  constructor
  · -- Prove 0 is the greatest element in the image of f over Icc 0 2
    constructor
    · -- Show that 0 belongs to the image
      use 2
      constructor
      · -- Show that 2 ∈ Icc 0 2
        exact ⟨by norm_num, by norm_num⟩
      · -- Show that f 2 = 0
        rw [hf]
        norm_num
        <;> simp [exp_pos]
        <;> norm_num
    · -- Show that 0 is an upper bound
      intro y
      rintro ⟨x, hx, hfx⟩
      rw [hf] at hfx
      simp at hfx
      rcases hx with ⟨hx0, hx1⟩
      have h1 : (x - 2) * exp x ≤ 0 := by
        have h2 : exp x > 0 := exp_pos x
        have h3 : x - 2 ≤ 0 := by linarith
        nlinarith [exp_pos x]
      linarith
  · -- Prove -exp 1 is the least element in the image of f over Icc 0 2
    constructor
    · -- Show that -exp 1 belongs to the image
      use 1
      constructor
      · -- Show that 1 ∈ Icc 0 2
        exact ⟨by norm_num, by norm_num⟩
      · -- Show that f 1 = -exp 1
        rw [hf]
        norm_num
        <;> simp [exp_pos]
        <;> ring_nf <;> norm_num
    · -- Show that -exp 1 is a lower bound
      intro y
      rintro ⟨x, hx, hfx⟩
      rw [hf] at hfx
      simp at hfx
      rcases hx with ⟨hx0, hx1⟩
      have h1 : (x - 2) * exp x ≥ - exp 1 := by
        -- Show that $f(x) + exp(1) \geq 0$ for $x \in [0, 2]$.
        have h4 : (x - 2) * exp x + exp 1 ≥ 0 := by
          -- To show $f(x) \geq -exp(1)$ we show $x \in [0,2]$ expression
          have h5 : exp (1 - x) ≥ 1 + (1 - x) := by
            linarith [Real.add_one_le_exp (1 - x)]
          have h4 : (2 - x) ≤ exp (1 - x) := by
            linarith
          -- Use positivity of exp functions
          have h7 : exp x * exp (1 - x) = exp 1 := by
            have h8 : exp x * exp (1 - x) = exp (x + (1 - x)) := by
              rw [← Real.exp_add]
              all_goals ring_nf
              <;> norm_num
            rw [h8]
            ring_nf
            all_goals norm_num
          have h9 : (2 - x) * exp x ≤ exp 1 := by
            have h8 : (2 - x) ≤ exp (1 - x) := by
              have h11 : exp (1 - x) ≥ 1 + (1 - x) := by
                linarith [Real.add_one_le_exp (1 - x)]
              linarith
            have h9 : exp x > 0 := exp_pos x
            have h8' : exp (1 - x) > 0 := exp_pos (1 - x)
            nlinarith [exp_nonneg x, exp_nonneg (1 - x), mul_nonneg (show (0 : ℝ) ≤ exp x by positivity) (show (0 : ℝ) ≤ exp (1 - x) by positivity), h7, sq_nonneg (exp x - exp (1 - x))]
          -- Transform the inequality to our form
          nlinarith [exp_pos x, exp_pos (1 : ℝ)]
        nlinarith
      linarith