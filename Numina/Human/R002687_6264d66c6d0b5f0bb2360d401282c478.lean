import Mathlib

open Real Set

/- 3. Let $f(x)$ be a monotonic function defined on $(0,+\infty)$. If for any $x \in(0,+\infty)$, we have $f\left[f(x)-2 \log _{2} x\right]=4$, then the solution set of the inequality $f(x)<6$ is $\qquad$. -/
theorem algebra_100350 {f : ℝ → ℝ}
  (h_f_mono : StrictMonoOn f (Ioi 0))
  (h : ∀ x ∈ Ioi 0, f x - 2 * logb 2 x ∈ Ioi 0 ∧ f (f x - 2 * logb 2 x) = 4) :
  {x | x ∈ Ioi 0 ∧ f x < 6} = Ioo 0 4 := by

  have h_log: logb 2 4 = 2 := by
    rw [(by norm_num : 4=(2:ℝ)^(2:ℝ))]
    rw [logb_rpow_eq_mul_logb_of_pos (by norm_num)]
    simp

  let a := f 1

  have ⟨ha1, ha2⟩ : a ∈ Ioi 0 ∧ f a = 4 := by
    have ⟨ h1, h2 ⟩ := h 1 (by simp)
    simp at h1 h2
    unfold a
    exact ⟨h1, h2⟩

  have h_f_inj : InjOn f (Ioi 0) := StrictMonoOn.injOn h_f_mono

  have hf1: ∀ x ∈ Ioi 0, f x - 2 * logb 2 x = a := by
    intro x hx
    have ⟨ h1, h2 ⟩ := h x hx
    rw [← ha2] at h2
    apply h_f_inj at h2
    rw [h2]
    all_goals assumption


  let fa := fun x:ℝ => x
  let fb := fun x => logb 2 x
  let fc := fun x => 2 * logb 2 x
  let fd := fun x => x + 2 * logb 2 x

  have h_fa_mono : StrictMonoOn fa (Ioi 0) := by
    intro x1 hx1 x2 hx2 h
    unfold fa
    exact h

  have h_fb_mono : StrictMonoOn fb (Ioi 0) := by
    unfold StrictMonoOn
    intro x1 hx1 x2 hx2 h
    unfold fb
    rw [logb_lt_logb_iff (by norm_num) hx1 hx2]
    exact h

  have h_fc_mono : StrictMonoOn fc (Ioi 0) := by
    intro x1 hx1 x2 hx2 h
    unfold fc
    have := h_fb_mono hx1 hx2 h
    unfold fb at this
    linarith

  have h_fd_mono : StrictMonoOn fd (Ioi 0) := by
    exact StrictMonoOn.add h_fa_mono h_fc_mono

  have h_fd_inj : InjOn fd (Ioi 0) := StrictMonoOn.injOn h_fd_mono

  have ha3: a = 2 := by
    have h1 := hf1 a ha1
    rw [ha2] at h1

    have : fd a = fd 2 := by
      unfold fd
      nth_rw 1 [← h1]
      simp
      norm_num

    apply h_fd_inj at this
    . exact this
    . exact ha1
    . simp

  have hf2 : ∀ x ∈ Ioi 0, f x = 2 + 2 * logb 2 x := by
    intro x hx
    have h1 := hf1 x hx
    rw [ha3] at h1
    linarith


  ext x
  simp
  intro hx
  constructor
  . intro h
    rw [hf2 x hx] at h
    have : logb 2 x < 2 := by linarith
    nth_rw 2 [← h_log] at this
    rw [logb_lt_logb_iff (by norm_num) hx (by norm_num)] at this
    exact this

  . intro h
    have : 6 = f 4 := by
      have := hf1 4 (by norm_num)
      rw [h_log] at this
      rw [ha3] at this
      linarith

    rw [this]
    apply h_f_mono
    . exact hx
    . simp
    . exact h
