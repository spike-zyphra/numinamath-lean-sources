import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Basic

open Real

/-
  Solve the ODE
  \[
    y''(x) + y(x) = 0, \qquad y(0)=1,\;y'(0)=0.
  \]
  An obvious solution is `cos`.  The energy method shows *uniqueness*:

  1.  Put `g := cos - y`.
  2.  `g`` satisfies the *same* ODE but with *zero* initial data.
  3.  Introduce the energy
        \[E(x) := g(x)^2 + g'(x)^2.\]
  4.  Compute `E'` to get `E' = 0`; hence `E` is constant.
  5.  Because `E(0)=0` this constant is `0`, so `E ≡ 0`.
  6.  A sum of two squares is `0` iff each term is, hence `g ≡ 0`.
  7.  Therefore `y ≡ cos`.
-/

theorem calculus_187069
    {y : ℝ → ℝ}
    {hy : ContDiff ℝ 2 y}
    (hODE : ∀ x, deriv (deriv y) x + y x = 0)
    (h0   : y 0 = 1)
    (h'0  : deriv y 0 = 0) :
    y = fun x ↦ Real.cos x := by

  ------------------------------------------------------------
  -- **Step 1.**  Define g := cos − y.
  ------------------------------------------------------------
  let g : ℝ → ℝ := fun x => Real.cos x - y x

  ------------------------------------------------------------
  -- **Step 2.**  Show g solves the same ODE and has zero data.
  --     Informal: Since both cos and y satisfy y''+y=0, their
  --     difference does too; g(0)=0 and g'(0)=0 by the given
  --     initial conditions for y and cos.
  ------------------------------------------------------------
  have gODE : ∀ x, deriv (deriv g) x + g x = 0 := by
    intro x
    dsimp [g]
    let fu : ℝ → ℝ := deriv fun x => cos x - y x
    /- We compute the derivatives explicitly, mirroring the
       informal argument “both terms satisfy the ODE, so does
       their difference”. -/
    have hfu : fu = fun x => -sin x - (deriv y x) := by
      simp [fu]
      ext x
      rw [deriv_sub]
      simp
      apply Differentiable.cos
      simp
      apply ContDiff.differentiable hy
      simp
    have hfu'' : ∀ x, (deriv fu) x = -cos x - (deriv (deriv y) x) := by
      intro x
      rw [hfu]
      rw [deriv_sub]
      simp
      · simp
      · have ha : (deriv y) = fun x => iteratedDeriv 1 y x := by
          simp
        rewrite [ha]
        apply (ContDiff.differentiable_iteratedDeriv 1 hy); simp

    have hcos : deriv (deriv fun t ↦ Real.cos t) x =
      -Real.cos x := by simp

    -- Assemble the equality (g'' + g = 0).
    rw [hfu'']
    linarith [hODE x]

  -- Zero initial data for g.
  have g0  : g 0 = 0      := by simp [g, h0]
  have g0' : deriv g 0 = 0 := by
    simp [g, deriv_sub, h'0, Real.deriv_cos]
    rw [deriv_sub]
    rw [h'0]
    simp
    · simp
    · apply (ContDiff.differentiable hy); simp

  ------------------------------------------------------------
  -- **Step 3.**  Energy function E := g² + g'².
  ------------------------------------------------------------
  let E : ℝ → ℝ := fun x ↦ (g x)^2 + (deriv g x)^2

  -- We will need smoothness of g later.
  have hg : ContDiff ℝ 2 g := by
        simp [g]
        apply ContDiff.sub
        apply ContDiff.cos
        -- `y` is C² by hypothesis.
        apply contDiff_id
        exact hy

  ------------------------------------------------------------
  -- **Step 4.**  Show E' = 0, hence E is constant.
  --     Informal: A direct differentiation gives
  --       E' = 2 g g' + 2 g'' g' = 2 g'(g + g'') = 0.
  ------------------------------------------------------------
  have hE' : ∀ x, deriv E x = 0 := by
    intro x
    simp [E]
    rw [deriv_add]
    rw [deriv_pow'']
    rw [deriv_pow'']
    simp
    -- Factor 2*g' and substitute g'' + g = 0.
    have factor : 2 * g x * deriv g x + 2 * deriv g x * deriv (deriv g) x =
        (2 * deriv g x) * (deriv (deriv g) x + g x) := by ring
    rw [factor]
    rw [gODE x]
    ring
    -- Routine smoothness obligations below.
    all_goals
      try
        (rewrite [<- iteratedDeriv_one])
      try
        (apply (ContDiff.differentiable_iteratedDeriv 1 hg)); simp
      try
        (apply ContDiff.differentiable hg); simp
      try
        apply Differentiable.pow
        apply ContDiff.differentiable hg
        simp
    apply Differentiable.pow
    apply ContDiff.differentiable_iteratedDeriv 1 hg
    simp

  ------------------------------------------------------------
  -- **Step 5.**  E is identically zero because E(0)=0.
  ------------------------------------------------------------
  have hE : ∀ x, E x = 0 := by
    -- First: show E is constant.
    have hconst : ∀ x y, E x = E y := by
      -- `is_const_of_deriv_eq_zero` needs C¹ smoothness of `E`.
      apply is_const_of_deriv_eq_zero _ hE'
      -- Prove C¹ smoothness of E (straightforward).
      simp [E] at *
      have hEcont : ContDiff ℝ 1 E := by
        simp [E]
        apply ContDiff.add _ _
        · apply ContDiff.pow
          have two_eq_1p1 : (2 : WithTop ℕ∞) = 1 + 1 := by rfl
          rewrite [two_eq_1p1] at hg
          apply ContDiff.one_of_succ hg
        · apply ContDiff.pow
          have deriv_eq : (deriv g) = deriv^[1] g := by simp
          rw [deriv_eq]
          apply ContDiff.iterate_deriv' 1
          simp
          exact hg
      simp [E] at hEcont
      apply ContDiff.differentiable hEcont; simp
    -- Evaluate the constant at 0.
    have hE0 : E 0 = 0 := by
      simp [E, g0, g0']
    intro x; simpa [hE0] using hconst x 0

  ------------------------------------------------------------
  -- **Step 6.**  Since E = g² + g'² = 0, each square vanishes → g = 0.
  ------------------------------------------------------------
  have hg_zero : ∀ x, g x = 0 := by
    intro x
    have hEx := hE x
    simp [E] at hEx
    -- A sum of two squares is zero iff both squares are zero.
    simp [E] at hE
    repeat (rw [pow_two] at hEx)
    rw [mul_self_add_mul_self_eq_zero] at hEx
    apply And.left hEx

  ------------------------------------------------------------
  -- **Step 7.**  Conclude y = cos.
  ------------------------------------------------------------
  funext x
  have := hg_zero x
  simpa [g] using (by
    have h := this
    simpa [g] using congrArg (fun t => Real.cos x - t) (congrArg id h))
  -- `linarith` was previously used here, but a simple rewrite suffices.
