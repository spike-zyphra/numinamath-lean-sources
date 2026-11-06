import Mathlib

open Real Set
open scoped BigOperators

/- Given the function $f(x)=\sin(3x+3\varphi)-2\sin(x+\varphi)\cos(2x+2\varphi)$, where $|\varphi| < \pi$, if $f(x)$ is monotonically decreasing in the interval $\left( \frac{\pi}{6},\frac{2\pi}{3} \right)$, then the maximum value of $\varphi$ is ______. -/
theorem algebra_9007 {g: ℝ → ℝ → ℝ} (hg: g = fun φ x => sin (3 * x + 3 * φ) - 2 * sin (x + φ) * cos (2 * x + 2 * φ)) : IsGreatest {φ : ℝ |  (|φ| < π ∧ AntitoneOn (g φ) (Set.Ioo (π / 6) (2 * π / 3)))} (5*π/6) := by
  -- simp at f(x)=g(φ,x) by using sin(A+B)=sinAcosB+sinBcosA and sin(A-B)=sinAcosB-sinBcosA
  have hf: ∀φ:ℝ, g φ = (fun x => sin (3 * x + 3 * φ) - 2 * sin (x + φ) * cos (2 * x + 2 * φ)) := by
    rw [hg]
    intro φ
    simp
  have hf': ∀φ:ℝ, (fun x => sin (3 * x + 3 * φ) - 2 * sin (x + φ) * cos (2 * x + 2 * φ)) = (fun x => sin (x+φ)) := by
    intro φ
    funext x
    have h1:   sin (3 * x + 3 * φ) = sin (2*x+2*φ) * cos (x+φ) +  cos (2*x+2*φ) * sin (x+φ) := by
      have:  3 * x + 3 * φ = (2*x+2*φ)+(x+φ) := by ring
      rw [this]
      apply sin_add (2*x+2*φ) (x+φ)
    have h2: sin (2 * x + 2 * φ) * cos (x + φ) + cos (2 * x + 2 * φ) * sin (x + φ) - 2 * sin (x + φ) * cos (2 * x + 2 * φ) = sin (2*x+2*φ) * cos (x+φ) - cos (2*x+2*φ) * sin (x+φ)  := by ring
    have h3: x+φ = (2*x+2*φ) - (x+φ) := by ring
    rw [h1, h2]
    nth_rewrite 3 [h3]
    symm
    apply sin_sub
  -- now, hmono says sin(x+φ) mono on (π/6,2π/3)
  -- we know that function sin is mono on (-π/2, π/2) and (π/2, 3π/2). so we can solve the range of φ
  rw [IsGreatest]
  simp
  -- prove 5π/6 satisfies the condition
  have hex:(|5 * π / 6| < π ∧ AntitoneOn (g (5 * π / 6)) (Ioo (π / 6) (2 * π / 3))) := by
    have h1: |5 * π / 6| < π := by
      rw [abs_lt]
      have ht1: -π < 5 * π / 6 := by linarith [pi_pos]
      have ht2: 5 * π / 6 < π := by linarith [pi_pos]
      exact ⟨ht1, ht2⟩
    have h2: AntitoneOn (g (5 * π / 6)) (Ioo (π / 6) (2 * π / 3)) := by
      intro x1 hx1 x2 hx2 hx1x2
      simp at hx1 hx2
      rw [hf, hf']
      simp
      -- sin is monotone on (0,π/2), and x+5π/6 is at (π,3π/2), so we let them sub π, and use monotone of sin to show antitone.
      have ht1: sin (x1 + 5 * π / 6) = -sin ((x1 + 5 * π / 6) - π) := by
        symm
        have: sin ((x1 + 5 * π / 6) - π) = -sin (x1 + 5 * π / 6) := sin_sub_pi ((x1 + 5 * π / 6))
        rw [this]; simp
      have ht2: sin (x2 + 5 * π / 6) = -sin ((x2 + 5 * π / 6) - π) := by
        symm
        have: sin ((x2 + 5 * π / 6) - π) = -sin (x2 + 5 * π / 6) := sin_sub_pi ((x2 + 5 * π / 6))
        rw [this]; simp
      rw [ht1, ht2]
      have hhx1: π < (x1 + 5 * π / 6) ∧ (x1 + 5 * π / 6) < 3*π/2 := by
        have hl: π < (x1 + 5 * π / 6) := by linarith [pi_pos, hx1.left]
        have hr: (x1 + 5 * π / 6) < 3*π/2 := by linarith [pi_pos, hx1.right]
        exact ⟨hl,hr⟩
      have hhx2: π < (x2 + 5 * π / 6) ∧ (x2 + 5 * π / 6) < 3*π/2 := by
        have hl: π < (x2 + 5 * π / 6) := by linarith [pi_pos, hx2.left]
        have hr: (x2 + 5 * π / 6) < 3*π/2 := by linarith [pi_pos, hx2.right]
        exact ⟨hl,hr⟩
      have: sin (x1 + 5 * π / 6 - π) ≤ sin (x2 + 5 * π / 6 - π) := by
        have htt1: (x1 + 5 * π / 6 - π) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
          simp
          have hl: π ≤ x1 + 5 * π / 6 + π / 2 := by linarith [hhx1,pi_pos]
          have hr: x1 + 5 * π / 6 ≤ π / 2 + π := by linarith [hhx1,pi_pos]
          exact ⟨hl,hr⟩
        have htt2: (x2 + 5 * π / 6 - π) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
          simp
          have hl: π ≤ x2 + 5 * π / 6 + π / 2 := by linarith [hhx2,pi_pos]
          have hr: x2 + 5 * π / 6 ≤ π / 2 + π := by linarith [hhx2,pi_pos]
          exact ⟨hl,hr⟩
        have htt3: x1 + 5 * π / 6 - π ≤ x2 + 5 * π / 6 - π := by linarith [hx1x2]
        have mono_sin: MonotoneOn Real.sin (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) := StrictMonoOn.monotoneOn strictMonoOn_sin
        apply mono_sin htt1 htt2 htt3
      linarith [this]
    exact ⟨h1, h2⟩
  -- next, we show 5π/6 is an upperbound.
  have hmax:  5 * π / 6 ∈ upperBounds {φ | |φ| < π ∧ AntitoneOn (g φ) (Ioo (π / 6) (2 * π / 3))} := by
    rw [upperBounds]
    simp
    intro φ h antitone_f
    rw [hf, hf'] at antitone_f
    by_contra! lower_φ
    have upper_φ: φ < π := by
      have: |φ| = φ := by
        have: 0 ≤ φ := by linarith [pi_pos, lower_φ]
        exact abs_of_nonneg this
      rwa [this] at h
    -- if 5π/6 is not an upperbound, then we can use antitone of f to get a contradiction.
    -- choose x1,x2 such that (x+φ-π) close to π or π/2
    let y := φ - 5*π/6
    have y_def: y = φ-5*π/6 := rfl
    have ypos: 0 < y := by
      rw [y_def]; linarith
    have ylt: y < π / 6 := by
      rw [y_def]; linarith
    let x1 := 2*π/3 - y/2
    have x1_def: x1 = 2*π/3 - y/2 := rfl
    let x2 := 2*π/3 - y/4
    have x2_def: x2 = 2*π/3 - y/4 := rfl
    have hx1x2: x1 < x2 := by
      rw [x1_def, x2_def]; linarith [ypos]
    -- we show that if x1 < x2, then f(x1) ≥ f(x2) by antitone.
    -- however, we also have f(x1) < f(x2) by strictmono of sin function. and they cannot be equal. so we get a contradiction.
    have not_antif: ¬ AntitoneOn (fun x => sin (x + φ)) (Ioo (π / 6) (2 * π / 3)) := by
      rw [AntitoneOn]
      push_neg
      use x1
      have hx1: x1 ∈ Ioo (π / 6) (2 * π / 3) := by
        simp
        rw [x1_def]
        have hl:  π / 6 < 2 * π / 3 - y / 2 := by linarith [ylt]
        have hr:  2 * π / 3 - y / 2 < 2 * π / 3 := by linarith
        exact ⟨hl,hr⟩
      have hh: ∃ b ∈ Ioo (π / 6) (2 * π / 3), x1 ≤ b ∧ sin (x1 + φ) < sin (b + φ) := by
        use x2
        have hx2: x2 ∈ Ioo (π / 6) (2 * π / 3) := by
          simp
          rw [x2_def]
          have hl:  π / 6 < 2 * π / 3 - y / 4 := by linarith [ylt]
          have hr:  2 * π / 3 - y / 4 < 2 * π / 3 := by linarith
          exact ⟨hl,hr⟩
        have hx1x2':  x1 ≤ x2 := le_of_lt hx1x2
        have sinlt: sin (x1 + φ) < sin (x2 + φ) := by
          have ht1: sin (x1 + φ) = - sin (2*π - (x1+φ)) := by
            have: sin (2*π -(x1+φ)) = - sin (x1+φ) := sin_two_pi_sub (x1+φ)
            rw [this]; simp
          have ht2: sin (x2 + φ) = - sin (2*π-(x2+φ)) := by
            have: sin (2*π-(x2+φ)) = - sin (x2+φ) := sin_two_pi_sub (x2+φ)
            rw [this]; simp
          rw [ht1, ht2]
          have ht3: sin (2 * π - (x1 + φ)) > sin (2 * π - (x2 + φ)) := by
            have htt1: 2 * π - (x1 + φ) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
              simp
              have hl:  x1 + φ ≤ 2 * π + π / 2 := by linarith
              have hr:  2 * π ≤ π / 2 + (x1 + φ) := by linarith
              exact ⟨hl,hr⟩
            have htt2: 2 * π - (x2 + φ) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
              simp
              have hl:  x2 + φ ≤ 2 * π + π / 2 := by linarith
              have hr:  2 * π ≤ π / 2 + (x2 + φ) := by linarith
              exact ⟨hl,hr⟩
            have htt3: 2 * π - (x1 + φ) > 2 * π - (x2 + φ) := by linarith
            apply strictMonoOn_sin htt2 htt1 htt3
          linarith [ht3]
        exact ⟨hx2, hx1x2', sinlt⟩
      exact ⟨hx1,hh⟩
    contradiction
  exact ⟨hex,hmax⟩