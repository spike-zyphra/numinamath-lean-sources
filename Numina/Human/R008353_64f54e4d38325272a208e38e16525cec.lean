import Mathlib

open Real Set
open scoped BigOperators

set_option maxHeartbeats 300000

/-Auxiliary lemma : if `MonotoneOn f s` and `MonotoneOn g (f '' s)`, then
  `MonotoneOn (g ∘ f) s`. -/
lemma MonotoneOn.comp_monotoneOn {α β γ : Type} {f : α → β} {g : β → γ}
  [Preorder α] [Preorder β] [Preorder γ] {s : Set α}
  (hf : MonotoneOn f s) (hg : MonotoneOn g (f '' s)) :
  MonotoneOn (g ∘ f) s := by
    intro x hx y hy hxy
    simp
    have h1 : f x ≤ f y := hf hx hy hxy
    exact hg ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ h1

/- Auxiliary lemma : if `AntitoneOn f s` and `MonotoneOn g (f '' s)`, then
  `AntitoneOn (g ∘ f) s `. -/
lemma AntitoneOn.comp_antitoneOn {α β γ : Type} {f : α → β} {g : β → γ}
  [Preorder α] [Preorder β] [Preorder γ] {s : Set α}
  (hf : AntitoneOn f s) (hg : MonotoneOn g (f '' s)) :
  AntitoneOn (g ∘ f) s := by
    intro x hx y hy hxy
    simp
    have h1 : f y ≤ f x := hf hx hy hxy
    exact hg  ⟨y, hy, rfl⟩ ⟨x, hx, rfl⟩ h1

/- Find the maximum and minimum values of the function $y=\lg(\sin^2x+2\cos x+2)$ for $$x\in\left[-\frac{\pi}{6}, \frac{2\pi}{3}\right].$$-/
theorem algebra_9394 (f : ℝ → ℝ) (hf : f = λ x => logb 10 (sin x ^ 2 + 2 * cos x + 2))
  (x : ℝ) : IsLeast {f x | x ∈ Icc (-π/6) (2*π/3)} (logb 10 (7 / 4)) ∧
  IsGreatest {f x | x ∈ Icc (-π/6) (2*π/3)} (logb 10 4) := by
    -- Auxiliary lemma : when -6 / π < x and x < 2π/3, 0 < sin x ^ 2 + 2 * cos x + 2.
    have aux : ∀ x ∈ Icc (-π/6) (2*π/3), 0 < sin x ^ 2 + 2 * cos x + 2 := by
      intro x hx
      calc _ < 2 * cos x + 2 := by
            have : -1 < cos x := by
              have := Real.neg_one_le_cos x
              have cosxne: cos x ≠ -1 := by
                contrapose! hx
                obtain ⟨k, hk⟩ := Real.cos_eq_neg_one_iff.1 hx
                simp
                intro h1
                have : 0 ≤ k := by
                  have := hk ▸ h1
                  contrapose! this
                  ring_nf
                  nth_rw 1 [←mul_one π]
                  rw [mul_assoc, ←mul_add]
                  refine (mul_lt_mul_left pi_pos).2 ?_
                  calc
                    _ ≤ (1 : ℝ)+ -2 := by
                      have : (k : ℝ) ≤ -1 := by
                        norm_cast; simp; exact Int.le_sub_one_of_lt this
                      simp; linarith [this]
                    _ < _ := by linarith
                have : π ≤ x := by
                  have : 0 ≤ (k : ℝ) := by norm_cast
                  rw [←hk]; nth_rw 1 [←add_zero π]
                  refine (add_le_add_iff_left π).mpr ?_
                  exact mul_nonneg this (by positivity)
                exact lt_of_lt_of_le (by ring_nf; linarith [pi_pos]) this
              exact lt_of_le_of_ne this (id (Ne.symm cosxne))
            linarith
           _ ≤ _ := by simp; positivity
    -- f can be viewed as the composition of `logb 10` and `in ^ 2 + 2 * cos + 2`.
    have aux1 : f = λ x => (logb 10 ∘ (sin ^ 2 + 2 * cos + 2)) x:= by simp [hf]

    -- the function y = 3 - x ^ 2 + 2 * x is monotone when -1 < x and x < 1.
    have aux2 : MonotoneOn (fun x ↦ 3 - x ^ 2 + 2 * x) (Icc (-1 : ℝ) 1) := by
      intro x hx y hy hxy
      simp
      have h4 : (y + x - 2) * (y - x) ≤ 0 := by
        apply mul_nonpos_iff.2
        right
        simp_all
        linarith
      linarith

    -- By the above lemma, f is monotone on `Icc (-π/6) 0`.
    have fmono : MonotoneOn f (Icc (-π/6) 0) := by
      rw [aux1]
      have h1 : (sin ^ 2 + 2 * cos + 2) '' (Icc (-π/6) 0) ⊆ Ioi 0 := by
        intro x hx
        obtain ⟨x0, hx0⟩ := hx
        simp  [←hx0.2]
        exact aux x0 (by simp_all; linarith)
      apply MonotoneOn.comp_monotoneOn
      · have h2 : sin ^ 2 + 2 * cos + 2 = (fun x => 3 - x ^ 2 + 2 * x) ∘ cos := by
          funext x
          simp [Real.sin_sq]
          ring
        have h3 : cos '' Icc (-π / 6) 0 ⊆ Icc (-1) 1 := by
          rintro x ⟨y, hy, hxy⟩
          simp [←hxy]
          exact ⟨ neg_one_le_cos y, cos_le_one y⟩
        rw [h2]
        apply MonotoneOn.comp_monotoneOn
        · apply monotoneOn_of_deriv_nonneg
          · exact convex_Icc (-π / 6) 0
          · exact continuousOn_cos
          · refine Differentiable.differentiableOn <| differentiable_cos
          · intro x hx
            simp at hx ⊢
            refine sin_nonpos_of_nonnpos_of_neg_pi_le ?_ ?_ <;> linarith
        · exact MonotoneOn.mono aux2 h3
      · have : MonotoneOn (logb 10) (Ioi 0) :=
          StrictMonoOn.monotoneOn <| Real.strictMonoOn_logb (by linarith)
        exact MonotoneOn.mono this h1

    -- By the above lemma, f is antitone on `Icc 0 (2*π / 3)`.
    have fanti : AntitoneOn f (Icc 0 (2*π / 3)) := by
      rw [aux1]
      have h1 : (sin ^ 2 + 2 * cos + 2) '' (Icc 0 (2*π/3)) ⊆ Ioi 0 := by
        intro x hx
        obtain ⟨y, hy⟩ := hx
        simp [←hy.2]
        exact aux y (by simp_all; linarith)
      apply AntitoneOn.comp_antitoneOn
      · have h2 : sin ^ 2 + 2 * cos + 2 = (fun x => 3 - x ^ 2 + 2 * x) ∘ cos := by
          funext x
          simp [Real.sin_sq]
          ring
        have h3 : cos '' Icc 0 (2*π/3)⊆ Icc (-1) 1 := by
          rintro x ⟨y, hy, hxy⟩
          simp [←hxy]
          exact ⟨ neg_one_le_cos y, cos_le_one y⟩
        rw [h2]
        apply AntitoneOn.comp_antitoneOn
        · have := StrictAntiOn.antitoneOn <| Real.strictAntiOn_cos
          exact AntitoneOn.mono this (Set.Icc_subset_Icc le_rfl (by linarith [pi_pos]))
        · exact MonotoneOn.mono aux2 h3
      · have : MonotoneOn (logb 10) (Ioi 0) :=
          StrictMonoOn.monotoneOn <| Real.strictMonoOn_logb (by linarith)
        exact MonotoneOn.mono this h1

    -- the minimum of f in `Icc (-π/6) (2*π/3)` is `f (2 * π / 3) `.
    have fmin : f (2 * π / 3) = logb 10 (7 / 4) := by
      simp [hf]
      congr 1
      simp [mul_div_assoc, sin_two_mul (π / 3), cos_two_mul]
      ring_nf; simp; ring
    -- the maximum of f in `Icc (-π/6) (2*π/3)` is `f 0 `.
    have fmax : f 0 = logb 10 4 := by
      simp [hf]
      ring
    have fmin' : f (-π / 6) = logb 10 (9 / 4 + √3) := by
      simp [hf, neg_div, sin_neg]
      ring_nf
    -- Verify that  the maximum value of the function is $\lg4$ and the minimum value is $\lg\frac{7}{4}$.
    constructor <;> constructor <;> simp
    · -- `f (2 * π / 3) = logb 10 (7 / 4)`
      use (2 * π / 3)
      exact ⟨by simp; ring_nf; exact (mul_le_mul_left Real.pi_pos).2 (by linarith), fmin⟩
    · intro a ha
      simp at ha
      obtain ⟨y, hy1, hy2⟩ := ha
      rw [←hy2, ←fmin]
      by_cases hy3 : y ∈ Icc 0 (2*π/3)
      · exact fanti hy3 (by simp; linarith) hy3.2
      · replace hy3 : y ∈ Ico (-π/6) 0 := by simp_all
        have c1 : f (-π/6) ≤ f y :=
          fmono (by simp; linarith) (by simp_all; linarith) (by simp_all)
        have c2 : f (2 * π / 3) ≤ f (-π/6)  := by
          rw [fmin, fmin', Real.logb_le_logb (by simp) (by simp) (by positivity)]
          rw [←add_zero (7 / 4)]
          apply add_le_add <;> try linarith
          exact sqrt_nonneg 3
        linarith
    · -- `f 0 = logb 10 4 `
      use 0
      exact ⟨⟨by simp [neg_div, neg_le]; positivity, by positivity⟩, fmax⟩
    · intro a ha
      simp at ha
      obtain ⟨y, hy1, hy2⟩ := ha
      by_cases hy3 :  y ∈ Icc 0 (2*π/3)
      · rw [←hy2, ←fmax]
        exact fanti (by simp; linarith) hy3 (by simp_all)
      · replace hy3 : y ∈ Icc (-π/6) 0 := by simp_all; linarith
        rw [←hy2, ←fmax]
        exact fmono hy3 (by simp; linarith) (by simp_all)
