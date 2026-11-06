import Mathlib
open Real
/- Define $a$ ? $=(a-1) /(a+1)$ for $a \neq-1$. Determine all real values $N$ for which $(N ?) ?=\tan 15$. -/
theorem algebra_610960 (f : ℝ → ℝ) (N : ℝ) (hf : f = fun x => (x - 1) / (x + 1)) (hN : N ≠ -1) : f (f N) = tan (15 * π / 180) ↔ N = -2 - √3:= by

  -- First prove that tan(15°) = 2 - √3
  have h1 : tan (15 * π / 180) = 2 - √3:= by
    ring_nf
    -- Use the known value of tan(30°)
    have h2:= Real.tan_pi_div_six
    -- Apply the double angle formula for tangent
    have h3 : tan (2 * (π / 12)) = 2 * tan (π / 12) / (1 - tan (π / 12) ^ 2):= Real.tan_two_mul
    rw [show 2 * (π / 12) = π / 6 by ring] at h3
    rw [h2] at h3
    set t:= tan (π / 12) with ht
    clear_value t

    -- Establish necessary inequalities
    have g1 : π > 0:= by positivity
    -- Prove tan(π/12) is positive
    have ht1 : t > 0:= by
      rw [ht]
      refine tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)
    -- Prove tan(π/12) < tan(π/4)
    have ht2 : t < tan (π / 4):= by
      rw [ht]
      refine tan_lt_tan_of_nonneg_of_lt_pi_div_two (by linarith) (by linarith) (by linarith)
    rw [show tan (π / 4) = 1 by exact tan_pi_div_four] at ht2

    -- Prove 1 - t² ≠ 0
    have ht3 : 1 - t ^ 2 ≠ 0:= by
      by_contra H
      replace H : (1 - t) * (1 + t) = 0:= by linarith
      simp at H
      rcases H with H | H
      all_goals
        linarith
    field_simp at h3
    replace h3 : (t - 2 + √3) * (t + 2 + √3) = 0:= by
      ring_nf
      field_simp
      linarith
    have h4 : t + 2 + √3 ≠ 0:= by
      by_contra H
      have g1 : √3 > 0:= by positivity
      linarith
    simp [h4] at h3
    rw [show π * (1 / 12) = π / 12 by ring]
    linarith

  -- Prove both directions of the equivalence
  constructor
  -- Forward direction: if f(f(N)) = tan(15°), then N = -2 - √3
  .
    intro h
    rw [h1] at h
    set t:= f N with ht
    clear_value t
    simp [hf] at h
    have ht1 : t ≠ -1:= by
      by_contra H
      subst t
      simp [hf] at H
      replace hN : N + 1 ≠ 0:= by
        by_contra H
        replace H : N = -1:= by linarith
        trivial
      field_simp at H
      replace H : N = 0:= by linarith
      subst N
      simp [hf] at h
      replace h : 2 = √3:= by linarith
      replace h : 2 ^ 2 = √3 ^ 2:= by rw [h]
      field_simp at h
      linarith
    replace ht1 : t + 1 ≠ 0:= by
      by_contra H
      replace H : t = -1:= by linarith
      trivial
    field_simp at h
    replace h : (√3 - 1) * (t - √3) = 0:= by ring_nf ; field_simp ; linarith
    have g1 : √3 - 1 ≠ 0:= by
      by_contra H
      have g1 : √3 > 1:= by refine lt_sqrt_of_sq_lt (by linarith)
      linarith
    simp [g1] at h
    replace h : t = √3:= by linarith
    subst t
    simp [hf] at h
    replace hN : N + 1 ≠ 0:= by
      by_contra H
      replace H : N = -1:= by linarith
      trivial
    field_simp at h
    replace h : (√3 - 1) * (N + 2 + √3) = 0:= by ring_nf ; field_simp ; linarith
    simp [g1] at h
    linarith

  -- Reverse direction: if N = -2 - √3, then f(f(N)) = tan(15°)
  .
    intro h
    rw [h1]
    have h2 : f N = √3:= by
      have g1 : N + 1 ≠ 0:= by
        by_contra H
        subst N
        have g1 : √3 > 0:= by positivity
        linarith
      simp [hf]
      field_simp
      subst N
      ring_nf
      field_simp
      linarith
    rw [h2]
    simp [hf]
    field_simp
    ring_nf
    field_simp
    linarith
