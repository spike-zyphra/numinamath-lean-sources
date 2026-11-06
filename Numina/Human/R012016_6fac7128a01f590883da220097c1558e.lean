import Mathlib
open Nat Real
noncomputable section

/-Find all twice differentiable functions $f(x)$ such that $f^{\prime \prime}(x)=0, f(0)=19$, and $f(1)=99$.-/
theorem calculus_12345 (f : ℝ → ℝ) (hf_diff : ∀ x, DifferentiableAt ℝ f x)
  (hf_second_diff : ∀ x, DifferentiableAt ℝ (deriv f) x)
  (hf_second_deriv : ∀ x, deriv (deriv f) x = 0)
  (hf_at_zero : f 0 = 19) (hf_at_one : f 1 = 99) :
  ∀ x, f x = 80 * x + 19 := by
  -- Prove that $f'(x)$ is a constant.
  have h_deriv_const : ∃ c, ∀ x, deriv f x = c := by
    have h_deriv_diff : ∀ x, DifferentiableAt ℝ (deriv f) x := hf_second_diff
    have h_deriv_zero : ∀ x, deriv (deriv f) x = 0 := hf_second_deriv
    have h_deriv_eq : ∀ x, deriv f x = deriv f 0 := by
      let g := deriv f
      have h_g_diff : Differentiable ℝ g := fun x => h_deriv_diff x
      have h_g_deriv : ∀ x, deriv g x = 0 := h_deriv_zero
      have h_g_const := is_const_of_deriv_eq_zero h_g_diff h_g_deriv
      intro x
      have h_g_x_eq_zero : g x = g 0 := h_g_const x 0
      exact h_g_x_eq_zero
    exact ⟨deriv f 0, h_deriv_eq⟩

  -- Prove that $f(x)$ is a linear function.
  have h_linear : ∃ a b, ∀ x, f x = a * x + b := by
    cases h_deriv_const with
    | intro c hc =>
      have h_deriv_eq : ∀ x, deriv f x = c := hc
      have h_linear' : ∃ a b, ∀ x, f x = a * x + b := by
        have h_antideriv : ∀ x, f x = c * x + (f 0) := by
          intro x
          let h := fun x => f x - c * x
          have h_diff : Differentiable ℝ h := by
            intro x
            apply DifferentiableAt.sub
            · exact hf_diff x
            · exact (differentiableAt_id).const_mul c
          have h_deriv : ∀ x, deriv h x = 0 := by
            intro x
            have h_deriv_h : deriv h x = deriv f x - deriv (fun x => c * x) x := by
              apply deriv_sub (hf_diff x) ((differentiableAt_id).const_mul c)
            have h_deriv_cx : deriv (fun x => c * x) x = c := by
              have h_has_deriv : HasDerivAt (fun y ↦ c * id y) (c * 1) x := (hasDerivAt_id x).const_mul c
              rw [mul_one] at h_has_deriv
              exact h_has_deriv.deriv
            rw [h_deriv_eq x, h_deriv_cx] at h_deriv_h
            simp at h_deriv_h
            exact h_deriv_h
          have h_const := is_const_of_deriv_eq_zero h_diff h_deriv
          have h_eq : ∀ x, h x = h 0 := by
            intro x
            exact h_const x 0
          have h_x : h x = f x - c * x := rfl
          have h_zero : h 0 = f 0 := by
            have h_zero_def : h 0 = f 0 - c * 0 := rfl
            rw [mul_zero] at h_zero_def
            simp at h_zero_def
            exact h_zero_def
          have h_eq_x : h x = h 0 := h_eq x
          rw [h_x, h_zero] at h_eq_x
          linarith
        exact ⟨c, f 0, h_antideriv⟩
      exact h_linear'

  -- Use $f(0) = 19$ to determine $b = 19$.
  have h_b_eq_19 : ∃ a, ∀ x, f x = a * x + 19 := by
    cases h_linear with
    | intro a ha =>
      cases ha with
      | intro b hb =>
        have h_at_zero : f 0 = b := by
          have h_eq : f 0 = a * 0 + b := hb 0
          simp at h_eq
          exact h_eq
        have h_b_eq : b = 19 := by
          exact Eq.trans h_at_zero.symm hf_at_zero
        have h_final : ∀ x, f x = a * x + 19 := by
          intro x
          have h_eq : f x = a * x + b := hb x
          rw [h_b_eq] at h_eq
          exact h_eq
        exact ⟨a, h_final⟩

  -- Use $f(1) = 99$ to determine $a = 80$.
  have h_a_eq_80 : ∀ x, f x = 80 * x + 19 := by
    cases h_b_eq_19 with
    | intro a ha =>
      have h_at_one : f 1 = a + 19 := by
        have h_eq : f 1 = a * 1 + 19 := ha 1
        simp at h_eq
        exact h_eq
      have h_a_eq : a = 80 := by
        have h_eq : a + 19 = 99 := by
          rw [← h_at_one, hf_at_one]
        have h_sub : a = 99 - 19 := by
          exact eq_sub_of_add_eq h_eq
        have h_calc : (99 : ℝ) - 19 = 80  := by norm_num
        exact Eq.trans h_sub h_calc
      have h_final : ∀ x, f x = 80 * x + 19 := by
        intro x
        have h_eq : f x = a * x + 19 := ha x
        rw [h_a_eq] at h_eq
        exact h_eq
      exact h_final

  -- Final conclusion.
  exact h_a_eq_80
