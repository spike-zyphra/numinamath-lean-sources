import Mathlib
open Real Finset Set
noncomputable section

-- Define the function $f$.
def f (x : ℝ) : ℝ := (1/2)^x + (2/3)^x + (5/6)^x

-- Auxiliary lemma: Prove that $a^x (0 < a < 1)$ is strictly decreasing.
lemma pow_decreasing (a : ℝ) (ha : 0 < a ∧ a < 1) :
    StrictAntiOn (fun (x : ℝ) => a^x) Set.univ := by
  intros x y _ _ hxy
  simp [StrictAntiOn]
  have ha_pos : 0 < a := ha.1
  have ha_lt_1 : a < 1 := ha.2
  have h_log_a_neg : log a < 0 := Real.log_neg ha_pos ha_lt_1
  have h_deriv : ∀ z, deriv (fun (x : ℝ) => a^x) z = a^z * log a := by
    intro z
    have h := Real.hasStrictDerivAt_const_rpow ha_pos z
    exact h.hasDerivAt.deriv
  have h_deriv_neg : ∀ z, deriv (fun (x : ℝ) => a^x) z < 0 := by
    intro z
    rw [h_deriv]
    exact mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos ha_pos z) h_log_a_neg
  have h_strict_anti : StrictAnti (fun (x : ℝ) => a^x) := by
    apply strictAnti_of_hasDerivAt_neg
    · intro z
      exact (Real.hasStrictDerivAt_const_rpow ha_pos z).hasDerivAt
    · intro z
      rw [← h_deriv]
      exact h_deriv_neg z
  exact h_strict_anti hxy

/-7. Let $t=\left(\frac{1}{2}\right)^{x}+\left(\frac{2}{3}\right)^{x}+\left(\frac{5}{6}\right)^{x}$, then the sum of all real solutions of the equation $(t-1)(t-2)(t-3)=0$ with respect to $x$ is $\qquad$ .-/
theorem algebra_2034567 :
    ∃ s : Finset ℝ, s = { x : ℝ | (f x - 1) * (f x - 2) * (f x - 3) = 0 } ∧ s.sum id = 4 := by
  -- Define solutions and rewrite $f(x)$.
  let solutions := { x : ℝ | (f x - 1) * (f x - 2) * (f x - 3) = 0 }
  have h_f_alt : ∀ x, f x = (3/6 : ℝ)^x + (4/6 : ℝ)^x + (5/6 : ℝ)^x := by
    intro x
    simp [f]
    norm_num

  -- Prove that $f(x)$ is strictly decreasing.
  have h_mono : StrictAntiOn (fun x => f x) Set.univ := by
    simp [StrictAntiOn, f]
    intros x y hxy
    have h_mono_1 : StrictAntiOn (fun (x : ℝ) => (1/2 : ℝ)^x) Set.univ := pow_decreasing (1/2) ⟨by norm_num, by norm_num⟩
    have h_mono_2 : StrictAntiOn (fun (x : ℝ) => (2/3 : ℝ)^x) Set.univ := pow_decreasing (2/3) ⟨by norm_num, by norm_num⟩
    have h_mono_3 : StrictAntiOn (fun (x : ℝ) => (5/6 : ℝ)^x) Set.univ := pow_decreasing (5/6) ⟨by norm_num, by norm_num⟩
    have h1 : (1/2 : ℝ)^x > (1/2 : ℝ)^y := by
      exact h_mono_1 (Set.mem_univ x) (Set.mem_univ y) hxy
    have h2 : (2/3 : ℝ)^x > (2/3 : ℝ)^y := by
      exact h_mono_2 (Set.mem_univ x) (Set.mem_univ y) hxy
    have h3 : (5/6 : ℝ)^x > (5/6 : ℝ)^y := by
      exact h_mono_3 (Set.mem_univ x) (Set.mem_univ y) hxy
    linarith

  -- Compute $f(0)$, $f(1)$, $f(3)$.
  have h_f_0 : f 0 = 3 := by simp [f];norm_num
  have h_f_1 : f 1 = 2 := by simp [f];norm_num
  have h_f_3 : f 3 = 1 := by simp [f];norm_num

  -- Prove the solution set is ${0, 1, 3}$.
  have h_solutions : solutions = {0, 1, 3} := by
    ext x
    simp only [solutions, Set.mem_setOf_eq]
    constructor
    · intro h
      have h_eq : f x = 1 ∨ f x = 2 ∨ f x = 3 := by
        have : (f x - 1) * (f x - 2) * (f x - 3) = 0 := h
        have h_zero : (f x - 1) = 0 ∨ (f x - 2) * (f x - 3) = 0 := by
          rw [mul_assoc] at this
          exact mul_eq_zero.mp this
        cases h_zero with
        | inl h1 =>
          left; linarith
        | inr h2 =>
          have : (f x - 2) = 0 ∨ (f x - 3) = 0 := by
            exact mul_eq_zero.mp h2
          cases this with
          | inl h2 => right; left; linarith
          | inr h3 => right; right; linarith
      cases h_eq with
      -- Verify through monotonicity that only these three solutions exist.
      | inl h1 =>
        have h_unique : ∀ y, f y = 1 → y = 3 := by
          intros y hy
          have h3 : f 3 = 1 := h_f_3
          have : x < y → f x > f y := h_mono (Set.mem_univ _) (Set.mem_univ _)
          by_contra h_ne
          cases lt_or_gt_of_ne h_ne with
          | inl h_lt =>
            have : f y > f 3 := h_mono (Set.mem_univ y) (Set.mem_univ 3) h_lt
            rw [h3, hy] at this
            linarith
          | inr h_gt =>
            have : f 3 > f y := h_mono (Set.mem_univ 3) (Set.mem_univ y) h_gt
            rw [h3, hy] at this
            linarith
        exact Or.inr (Or.inr (h_unique x h1))
      | inr h2 =>
        cases h2 with
        | inl h2 =>
          have h_unique : ∀ y, f y = 2 → y = 1 := by
            intros y hy
            have h1 : f 1 = 2 := h_f_1
            have : x < y → f x > f y := h_mono (Set.mem_univ _) (Set.mem_univ _)
            by_contra h_ne
            cases lt_or_gt_of_ne h_ne with
            | inl h_lt =>
              have : f y > f 1 := h_mono (Set.mem_univ y) (Set.mem_univ 1) h_lt
              rw [h1, hy] at this
              linarith
            | inr h_gt =>
              have : f 1 > f y := h_mono (Set.mem_univ 1) (Set.mem_univ y) h_gt
              rw [h1, hy] at this
              linarith
          exact Or.inr (Or.inl (h_unique x h2))
        | inr h3 =>
          have h_unique : ∀ y, f y = 3 → y = 0 := by
            intros y hy
            have h0 : f 0 = 3 := h_f_0
            have : x < y → f x > f y := h_mono (Set.mem_univ _) (Set.mem_univ _)
            by_contra h_ne
            cases lt_or_gt_of_ne h_ne with
            | inl h_lt =>
              have : f y > f 0 := h_mono (Set.mem_univ y) (Set.mem_univ 0) h_lt
              rw [h0, hy] at this
              linarith
            | inr h_gt =>
              have : f 0 > f y := h_mono (Set.mem_univ 0) (Set.mem_univ y) h_gt
              rw [h0, hy] at this
              linarith
          exact Or.inl (h_unique x h3)
    · intro h
      cases h with
      | inl h0 =>
        rw [h0, h_f_0]
        norm_num
      | inr h1 =>
        cases h1 with
        | inl h1 =>
          rw [h1, h_f_1]
          norm_num
        | inr h3 =>
          rw [h3, h_f_3]
          norm_num
  let solutions_fin : Finset ℝ := {0, 1, 3}
  have h_solutions_fin : solutions_fin.toSet = solutions := by
    simp [solutions_fin, h_solutions]

  -- Prove the sum is $4$.
  have h_sum : solutions_fin.sum id = 4 := by
    simp [solutions_fin]
    norm_num
  exists solutions_fin
