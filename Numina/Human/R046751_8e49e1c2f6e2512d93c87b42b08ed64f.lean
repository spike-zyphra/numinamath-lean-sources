import Mathlib

open Real Set
open scoped BigOperators

/-
Given the function $f(x) = 2\sin x \cdot \cos \left( x + \frac{\pi}{3} \right)$, this theorem solves two main problems:
(Ⅰ) Determine the intervals of monotonicity for $f(x)$.
-/
theorem algebra_9101_1 {f : ℝ → ℝ} (hf : f = λ x => 2 * sin x * cos (x + π / 3)) :
    (∀ k:ℤ,
        MonotoneOn f (Icc (- 5 / 12 * π + k * π) (1 / 12 * π + k * π)) ∧
        AntitoneOn f (Icc (1 / 12 * π + k * π) (7 / 12 * π + k * π))) := by

  -- Simplify the function using trigonometric identities:
  -- $f(x) = 2 \sin x \cos(x + \frac{\pi}{3})$ simplifies to $f(x) = \sin(2x + \frac{\pi}{3}) - \sqrt{3}/2$.
  have hf₀ x : 2 * sin x * cos (x + π / 3) = sin (2 * x + π / 3) - √3 / 2 := by
    calc
    2 * sin x * cos (x + π / 3) = 2 * sin x * (cos x * (1 / 2) - sin x * (√3 / 2)) := by rw [cos_add, cos_pi_div_three, sin_pi_div_three]
                              _ = 1 / 2 * (2 * sin x * cos x) - √3 * sin x ^ 2 := by ring
                              _ = 1 / 2 * sin (2 * x) - √3 * (1 / 2 - cos (2 * x) / 2) := by rw [sin_two_mul, sin_sq_eq_half_sub]
                              _ = sin (2 * x) * (1 / 2) + cos (2 * x) * (√3 / 2) - √3 / 2 := by ring
                              _ = sin (2 * x) * cos (π / 3) + cos (2 * x) * sin (π / 3) - √3 / 2 := by simp
                              _ = sin (2 * x + π / 3) - √3 / 2 := by rw [← sin_add]

  -- Prove that $f(x)$ alternates between monotone and antitone behavior on specified intervals.
  unfold MonotoneOn
  intro k
  constructor
  all_goals intro a ha b hb haleb
  all_goals simp [*, -one_div] at *
  all_goals generalize ha₁ : 2 * a + π / 3 = a₁
  all_goals generalize hb₁ : 2 * b + π / 3 = b₁

  . -- $f(x)$ is monotone on $[- \frac{5}{12} \pi + k \pi, \frac{1}{12} \pi + k \pi]$.
    generalize ha₂ : a₁ - k * (2 * π) = a₂
    generalize hb₂ : b₁ - k * (2 * π) = b₂
    have hsaleb₂ : sin a₂ ≤ sin b₂ := by
      -- Use the fact that the sine function is increasing in $[-\pi/2, \pi/2]$.
      apply sin_le_sin_of_le_of_le_pi_div_two; repeat linarith
    rw [← ha₂, ← hb₂] at hsaleb₂
    rw [← sin_sub_int_mul_two_pi a₁ k, ← sin_sub_int_mul_two_pi b₁ k]
    linarith

  . -- $f(x)$ is antitone on $[\frac{1}{12} \pi + k \pi, \frac{7}{12} \pi + k \pi]$.
    generalize ha₂ : a₁ - k * (2 * π) - π  = a₂
    generalize hb₂ : b₁ - k * (2 * π) - π  = b₂
    have hsaleb₂ : sin a₂ ≤ sin b₂ := by
      -- Use the fact that the sine function is increasing in $[-\pi/2, \pi/2]$.
      apply sin_le_sin_of_le_of_le_pi_div_two; repeat linarith
    rw [← ha₂, ← hb₂] at hsaleb₂
    rw [sin_sub_pi (a₁ - ↑k * (2 * π)), sin_sub_pi (b₁ - ↑k * (2 * π))] at hsaleb₂
    rw [← sin_sub_int_mul_two_pi a₁ k, ← sin_sub_int_mul_two_pi b₁ k]
    linarith


/- (Ⅱ) Find the maximum and minimum values of $f(x)$ in the interval $[0, \frac{\pi}{2}]$, as well as the $x$-values at which these extrema occur. -/
theorem algebra_9101_2 {f : ℝ → ℝ} (hf : f = λ x => 2 * sin x * cos (x + π / 3)) :
    IsGreatest (image f (Icc 0 (π / 2))) (1 - sqrt 3 / 2) ∧
    IsLeast (image f (Icc 0 (π / 2))) (- sqrt 3) ∧
    f (π / 12) = 1 - sqrt 3 / 2 ∧
    f (π / 2) = - sqrt 3 := by

  -- Simplify the function using trigonometric identities:
  -- $f(x) = 2 \sin x \cos(x + \frac{\pi}{3})$ simplifies to $f(x) = \sin(2x + \frac{\pi}{3}) - \sqrt{3}/2$.
  have hf₀ x : 2 * sin x * cos (x + π / 3) = sin (2 * x + π / 3) - √3 / 2 := by
    calc
    2 * sin x * cos (x + π / 3) = 2 * sin x * (cos x * (1 / 2) - sin x * (√3 / 2)) := by rw [cos_add, cos_pi_div_three, sin_pi_div_three]
                              _ = 1 / 2 * (2 * sin x * cos x) - √3 * sin x ^ 2 := by ring
                              _ = 1 / 2 * sin (2 * x) - √3 * (1 / 2 - cos (2 * x) / 2) := by rw [sin_two_mul, sin_sq_eq_half_sub]
                              _ = sin (2 * x) * (1 / 2) + cos (2 * x) * (√3 / 2) - √3 / 2 := by ring
                              _ = sin (2 * x) * cos (π / 3) + cos (2 * x) * sin (π / 3) - √3 / 2 := by simp
                              _ = sin (2 * x + π / 3) - √3 / 2 := by rw [← sin_add]



  constructor

  . -- Prove that $1 - \sqrt{3}/2$ is the maximum value of $f(x)$.
    constructor
    . -- Show that $f(\pi/12) = 1 - \sqrt{3}/2$.
      simp_all
      use π / 12
      constructor
      . constructor <;> nlinarith [pi_nonneg]
      . ring_nf; rw [← mul_div_assoc, mul_one]; simp
    . -- Show that $1 - \sqrt{3}/2$ is an upper bound for $f(x)$ in $[0, \frac{\pi}{2}]$.
      rintro z hz
      simp_all
      obtain ⟨x, _, hx₁⟩ := hz
      rw [← hx₁]
      linarith [sin_le_one (2 * x + π / 3)]

  . -- Prove that $-\sqrt{3}$ is the minimum value of $f(x)$.
    constructor
    constructor
    . -- Show that $f(\pi/2) = -\sqrt{3}$.
      simp_all
      use π / 2
      constructor
      . constructor <;> nlinarith [pi_nonneg]
      . ring_nf
        have : sin (π * (4 / 3)) = - (√3 / 2) := by
          calc
          sin (π * (4 / 3)) = sin (π / 3 + π) := by ring_nf
          _ = - (√3 / 2) := by simp
        rw [this]; ring
    . -- Show that $-\sqrt{3}$ is a lower bound for $f(x)$ in $[0, \frac{\pi}{2}]$.
      rintro z hz
      simp_all
      obtain ⟨x, hx₀, hx₁⟩ := hz
      rw [← hx₁]
      generalize hy : 2 * x + π / 3 = y
      by_cases hy₀ : y ≤ π / 2
      . -- Case $y ≤ \pi/2$: Prove using monotonicity of $\sin(y)$.
        have : sin (π / 3) ≤ sin y := by
          apply sin_le_sin_of_le_of_le_pi_div_two; repeat linarith
        rw [sin_pi_div_three] at this
        have : -√3 ≤ 0 := by norm_num
        linarith
      . -- Case $π / 2 < y$: Prove using monotonicity of $\sin(y)$.
        simp at hy₀
        rw [← cos_sub_pi_div_two]
        generalize hw : y - π / 2 = w
        have hw0 : cos (π / 3 + π / 2) ≤ cos w := by
          apply cos_le_cos_of_nonneg_of_le_pi; repeat linarith
        have hw1 : cos (π / 3 + π / 2) = - (√3 / 2) := by rw [cos_add_pi_div_two, sin_pi_div_three]
        rw [hw1] at hw0
        have : -√3 ≤ cos w - √3 / 2 := by
          calc
          -√3 = - √3 / 2 - √3 / 2 := by ring
            _ ≤ cos w - √3 / 2 := by linarith
        exact this

    -- Prove that f (π / 12) = 1 - √3 / 2 and f (π / 2) = -√3.
    constructor
    -- Simplify equations.
    all_goals simp_all
    all_goals ring_nf

    -- Prove that sin (π * (1 / 2)) = 1.
    have : sin (π * (1 / 2)) = 1 := by
      calc
      sin (π * (1 / 2)) = sin (π / 2) := by ring_nf
                      _ = 1 := by simp
    exact this

    -- Prove that sin (π * (4 / 3)) + √3 * (-1 / 2) = -√3.
    have : sin (π * (4 / 3)) + √3 * (-1 / 2) = -√3 := by
      calc
      sin (π * (4 / 3)) + √3 * (-1 / 2) = sin (π / 3 + π) - √3 / 2 := by ring_nf
                                      _ = - (√3 / 2) - √3 / 2 := by simp [sin_add_pi, sin_pi_div_three]
                                      _ = -√3 := by nlinarith
    exact this
