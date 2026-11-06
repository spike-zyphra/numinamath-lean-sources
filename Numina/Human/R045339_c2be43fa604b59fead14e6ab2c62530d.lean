import Mathlib

open Real Set
open scoped Real

/- When the function f(x) = 2sin(x) + cos(x) reaches its minimum value at x = θ, find the value of cos($$θ + \frac{π}{4}$$). -/
theorem algebra_9003 {f : ℝ → ℝ} (hf : f = λ x => 2 * sin x + cos x)
(θ : ℝ) (fmin: ∀x:ℝ, f x ≥ f θ) (hθ' : deriv f θ = 0) : cos (θ + π / 4) = sqrt 10 / 10 := by
have hderiv: deriv f = fun x => 2 * cos x - sin x := by
-- (cosx)'=-sinx and (sinx)'=cosx, so f'(x) = (2sinx+cosx)' = 2cosx-sinx
  have h1: deriv (fun x => 2 * sin x) = 2 * deriv sin := by
    funext x
    have ht: DifferentiableAt ℝ sin x := differentiableAt_sin
    apply deriv_const_mul
    apply ht
  have h2: deriv cos = -sin := by
    funext x
    apply Real.deriv_cos
  have h3: deriv (fun x => 2 * sin x + cos x) = deriv (fun x => 2 * sin x) + deriv (fun x => cos x) := by
    funext x
    have: ((deriv fun x => 2 * sin x) + deriv fun x => cos x) x = deriv (fun x => 2*sin x) x + deriv (fun x => cos x) x := by simp
    rw [this]
    have ht1: DifferentiableAt ℝ (fun y => 2 * sin y) x := by
      have: DifferentiableAt ℝ sin x := differentiableAt_sin
      exact DifferentiableAt.const_mul this 2
    have ht2: DifferentiableAt ℝ cos x := differentiableAt_cos
    exact deriv_add ht1 ht2
  rw [hf, h3, h1, h2]
  simp
  rfl
rw [hderiv] at hθ'
simp at hθ'
-- by hderiv, f'(x)=0 leads to 2cosx = sinx.
-- combine with (cosx)^2+(sinx)^2=1, we can solve sinx = ±2√5/5, cosx = ±√5/5
have h1: (cos θ - sin θ) = √5 / 5 := by
  have h1: sin θ = 2 * cos θ := by
    rw [← add_zero (sin θ), ← hθ']
    ring
  have h2: (2 * cos θ) ^ 2 + cos θ ^ 2 = (cos θ)^2 * 5 := by ring
  have h3: (sin θ)^2 + (cos θ)^2 = 1 := by simp
  rw [h1, h2] at h3
  have h4: cos θ = -(√5 / 5) := by
    have ht1:  (cos θ) ^ 2 = 1 / 5 := eq_one_div_of_mul_eq_one_left h3
    have ht2: 1/5 = (√5 / 5)^2 := by
      have: 5 = (√5)^2 := by simp
      ring_nf
      rw [← this]
      ring
    -- f(θ) is minimum not maximum, we can prove cosθ<0.
    by_cases signcos: cos θ ≥ 0
    have: sin θ ≥ 0 := by
      rw [h1]; linarith
    have hh1: f θ ≥ 0 := by
      rw [hf]; simp; linarith
    have hh2: f (-π) < 0 := by
      rw [hf]; simp
    have hh3: f θ > f (-π) := by linarith [hh1, hh2]
    have hh4: f (-π) ≥ f θ := fmin (-π)
    linarith [hh3, hh4]
    -- now cosθ < 0
    push_neg at signcos
    have ht3: 0 ≤ - cos θ := by linarith [signcos]
    have ht4: cos θ ^ 2 = (-cos θ)^2 := Eq.symm (neg_pow_two (cos θ))
    rw [ht2, ht4] at ht1
    have ht5: (-cos θ) = √5 / 5 := by
      have: 0 ≤ √5 / 5 := by
        have htt1: 0 ≤ (5:ℝ) := by norm_num
        have htt2: 0 ≤ √5 := sqrt_nonneg 5
        linarith [htt1, htt2]
      apply (sq_eq_sq ht3 this).mp ht1
    rw [← ht5]
    simp
  rw [h1, h4]
  ring
have h2: cos (θ + π / 4) = cos θ * cos (π/4) - sin θ * sin (π/4) := cos_add θ (π/4)
have h3: sin (π /4) = √2 / 2 := sin_pi_div_four
have h4: cos (π /4) = √2 / 2 := cos_pi_div_four
have h5: cos θ * (√2 / 2) - sin θ * (√2 / 2) = (cos θ - sin θ) * (√2 / 2) := by ring
have h6:  √10 / 10 = (√5 / 5) * (√2 / 2) := by
  have: √10 = √5 * √2 := by
    have: (10:ℝ) = 5*2 := by norm_num
    rw [this]
    simp
  rw [this]
  ring
rw [h2, h3, h4, h5, h6, h1]