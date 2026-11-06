import Mathlib

lemma s1 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
  (f : ℝ → ℝ) (h : ∀ x, Irrational x → f x = b * x)
  (h' : ∀ x, ¬Irrational x → f x = a * x) :
  Function.Injective f ↔ ¬Irrational (a / b) := by
  have h_left : ¬Irrational (a / b) → Function.Injective f := by
    intro h₁
    intro x y h₂
    -- Prove that f is injective by considering cases based on irrationality of x and y.
    by_cases hx : Irrational x
    · by_cases hy : Irrational y
      all_goals simp_all [h, h', Irrational]
      · -- If x is irrational and y is rational, derive a contradiction using the fact that a/b is rational.
        exfalso
        -- Use the fact that a/b is rational to show that x cannot be irrational if f(x) = f(y).
        have h₃ : (a / b : ℝ) ≠ 0 := by
          intro h₃
          apply ha
          field_simp [hb] at h₃ ⊢
          <;> linarith
        have h₄ : ∃ (q : ℚ), (a / b : ℝ) = q := by
          obtain ⟨aa, h₁⟩ := h₁
          exists aa
          symm
          exact h₁
        obtain ⟨q, h₅⟩ := h₄
        have h₆ : x = (a / b : ℝ) * y := by
          field_simp [hb] at h₂ ⊢
          rw [mul_comm, h₂]
          obtain ⟨ls, hy⟩ := hy
          have qq := h' ls
          rw [hy] at qq
          exact qq
        rw [h₅] at h₆
        have h₇ : ¬Irrational x := by
          rw [h₆]
          intro h₈
          obtain ⟨ax, hy⟩ := hy
          rw [←hy] at h₈
          simp at h₈
        exact h₇ (by simp [Irrational]; assumption)
    by_cases hy : Irrational y
    all_goals simp_all [h, h', Irrational]
    · -- If x is rational and y is irrational, derive a contradiction using the fact that a/b is rational.
      exfalso
      -- Use the fact that a/b is rational to show that y cannot be irrational if f(x) = f(y).
      have h₃ : (a / b : ℝ) ≠ 0 := by
        intro h₃
        apply ha
        field_simp [hb] at h₃ ⊢
        <;> linarith
      have h₄ : ∃ (q : ℚ), (a / b : ℝ) = q := by
        obtain ⟨aa, h₁⟩ := h₁
        exists aa
        symm
        exact h₁
      obtain ⟨q, h₅⟩ := h₄
      have h₆ : y = (a / b : ℝ) * x := by
        field_simp [hb] at h₂ ⊢
        rw [mul_comm, ←h₂]
        obtain ⟨ls, hx⟩ := hx
        have qq := h' ls
        rw [hx] at qq
        exact qq
      rw [h₅] at h₆
      have h₇ : ¬Irrational y := by
        rw [h₆]
        intro h₈
        obtain ⟨ay, hx⟩ := hx
        subst x
        simp [Irrational] at h₈
        have alx := h₈ (q * ay)
        simp at alx
      simp [Irrational] at h₇
      obtain ⟨kk, h₇⟩ := h₇
      subst y
      obtain ⟨ll, hx⟩ := hx
      subst x
      have := hy (q * ll)
      simp at this
    · -- If both x and y are rational, use the fact that a ≠ 0.
      apply mul_left_cancel₀ (sub_ne_zero.mpr ha)
      rw [sub_zero]
      obtain ⟨rx, hx⟩ := hx
      obtain ⟨ry, hy⟩ := hy
      subst x y
      rw [← h', h₂, h']

  have h_right : Function.Injective f → ¬Irrational (a / b) := by
    intro h_inj
    by_contra h_irrat
    -- Assume f is injective and a/b is irrational.
    have h₁ : f (a / b) = f 1 := by
      -- Prove that f(a/b) = f(1).
      have h₂ : f (a / b) = b * (a / b) := by
        apply h
        -- Prove that a/b is irrational.
        exact h_irrat
      have h₃ : f 1 = a * 1 := by
        apply h'
        -- Prove that 1 is not irrational.
        intro h_irrat_one
        exact h_irrat_one ⟨1, by simp⟩
      rw [h₂, h₃]
      -- Simplify the expressions.
      <;> ring_nf
      <;> field_simp [hb]
      <;> ring_nf
    -- Derive a contradiction using the injectivity of f.
    have h₂ : a / b ≠ (1 : ℝ) := by
      intro h_eq
      apply h_irrat
      rw [Irrational] at *
      push_neg at *
      use (1 : ℚ)
      <;> simp_all [Rat.cast_one]
      <;> field_simp [hb] at *
      <;> linarith
    have h₃ : (a / b : ℝ) ≠ 1 := h₂
    have h₄ : Function.Injective f := h_inj
    -- Apply the injectivity of f to get a contradiction.
    have h₅ : a / b = 1 := by
      apply h₄
      exact h₁
    contradiction
  
  have h_main : Function.Injective f ↔ ¬Irrational (a / b) := by
    constructor
    · -- Prove the forward direction: if f is injective, then ¬Irrational (a / b)
      intro h_inj
      exact h_right h_inj
    · -- Prove the backward direction: if ¬Irrational (a / b), then f is injective
      intro h_not_irrat
      exact h_left h_not_irrat
  
  exact h_main

theorem s2 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
  (f : ℝ → ℝ) (h : ∀ x, Irrational x → f x = b * x)
  (h' : ∀ x, ¬Irrational x → f x = a * x) :
  Function.Surjective f ↔ ¬Irrational (a / b) := by
  have h_imp : Function.Surjective f → ¬Irrational (a / b) := by
    intro h_surj
    by_contra h_irrat
    -- Assume for contradiction that `a / b` is irrational
    have h₁ : Irrational (a / b) := h_irrat
    -- Consider `y = b` and show that there is no `x` such that `f x = b`
    have h₂ : ∃ (x : ℝ), f x = b := h_surj b
    obtain ⟨x, hx⟩ := h₂
    by_cases hx_irrat : Irrational x
    · -- Case 1: `x` is irrational
      have h₃ : f x = b * x := h x hx_irrat
      rw [h₃] at hx
      have h₄ : b * x = b := by linarith
      have h₅ : x = 1 := by
        apply mul_left_cancel₀ hb
        linarith
      have h₆ : ¬Irrational (1 : ℝ) := by
        exact fun h₁ => h₁ ⟨1, by norm_num⟩
      exact h₆ (by simpa [h₅] using hx_irrat)
    · -- Case 2: `x` is rational
      have h₃ : f x = a * x := h' x hx_irrat
      rw [h₃] at hx
      have h₄ : a * x = b := by linarith
      have h₅ : x = b / a := by
        field_simp [ha] at h₄ ⊢
        <;> nlinarith
      have h₆ : Irrational (b / a) := by
        have h₇ : b / a = (a / b)⁻¹ := by
          field_simp [ha, hb]
          <;> ring
        rw [h₇]
        -- `a / b` is irrational, so its inverse is also irrational
        exact fun ⟨q, hq⟩ => h₁ ⟨q⁻¹, by
          rify; rw [hq];
          rw [inv_inv]
        ⟩
      -- `x = b / a` is irrational, but `x` is rational, contradiction
      exact h₆ (by rw [← h₅]; simp; simp [Irrational] at hx_irrat; exact hx_irrat)
  
  have h_conv : ¬Irrational (a / b) → Function.Surjective f := by
    intro h_not_irrat
    -- Assume `a / b` is not irrational (i.e., it is rational)
    have h₁ : ∃ (r : ℚ), (r : ℝ) = a / b := by
      by_cases h₂ : Irrational (a / b)
      · exfalso
        exact h_not_irrat h₂
      · -- `a / b` is not irrational, so it is rational
        simp only [Irrational, not_forall, not_not, exists_prop] at h₂
        obtain ⟨q, hq⟩ := h₂
        exact ⟨q, by simp_all [eq_comm]⟩
    obtain ⟨r, hr⟩ := h₁
    -- For any real number `y`, we need to find `x` such that `f x = y`
    have h_main : ∀ (y : ℝ), ∃ (x : ℝ), f x = y := by
      intro y
      by_cases h₁ : Irrational (y / b)
      · -- Case 1: y / b is irrational
        have h₂ : f (y / b) = y := by
          have h₃ : f (y / b) = b * (y / b) := h (y / b) h₁
          have h₄ : b * (y / b) = y := by
            field_simp [hb]
            <;> ring
          rw [h₃, h₄]
        refine' ⟨y / b, _⟩
        exact h₂
      · -- Case 2: y / b is not irrational (i.e., rational)
        have h₂ : ¬Irrational (y / b) := h₁
        have h₃ : f (y / a) = y := by
          have h₄ : ¬Irrational (y / a) := by
            -- Prove that y / a is not irrational (i.e., rational)
            have h₅ : a / b = (r : ℝ) := by
              linarith
            have h₆ : a = (r : ℝ) * b := by
              field_simp [hb] at h₅ ⊢
              <;> nlinarith
            have h₇ : y / a = (y / b) / (a / b) := by
              field_simp [ha, hb]
              <;> ring
            rw [h₇]
            have h₈ : (a / b : ℝ) = (r : ℝ) := by
              linarith
            rw [h₈]
            -- Since y / b is rational and r is rational, (y / b) / r is rational
            have h₉ : ¬Irrational (y / b) := h₂
            have h₁₀ : ∃ (q : ℚ), (q : ℝ) = y / b := by
              by_contra h₁₀
              have h₁₁ : Irrational (y / b) := by
                push_neg at h₁₀
                simp [Irrational]
                exact h₁₀
              contradiction
            rcases h₁₀ with ⟨q, hq⟩
            have h₁₁ : (q : ℝ) / r = ((q / r : ℚ) : ℝ) := by
              norm_cast
              <;> field_simp
              <;> ring_nf
              <;> norm_cast
            have h₁₂ : (y / b : ℝ) / r = (q : ℝ) / r := by
              rw [hq]
            have h₁₃ : ¬Irrational ((q : ℝ) / r) := by
              have h₁₄ : ∃ (q' : ℚ), (q' : ℝ) = (q : ℝ) / r := by
                exact ⟨q / r, by
                  norm_cast <;> field_simp <;> ring_nf <;> norm_cast⟩
              rcases h₁₄ with ⟨q', hq'⟩
              intro h₁₅
              rw [← hq'] at h₁₅
              simp [Irrational] at h₁₅
            have h₁₄ : ¬Irrational ((y / b : ℝ) / r) := by
              rw [h₁₂]
              exact h₁₃
            simpa [h₈] using h₁₄
          have h₅ : f (y / a) = a * (y / a) := h' (y / a) h₄
          have h₆ : a * (y / a) = y := by
            field_simp [ha]
            <;> ring
          rw [h₅, h₆]
        refine' ⟨y / a, _⟩
        exact h₃
    have h_surjective : Function.Surjective f := by
      rw [Function.Surjective]
      exact h_main
    exact h_surjective
  have h_final : Function.Surjective f ↔ ¬Irrational (a / b) := by
    constructor
    · -- Prove the forward direction: if f is surjective, then a/b is not irrational
      intro h_surj
      exact h_imp h_surj
    · -- Prove the backward direction: if a/b is not irrational, then f is surjective
      intro h_not_irrat
      exact h_conv h_not_irrat
  
  exact h_final

/- Take the function $f:\mathbb{R}\to \mathbb{R}$, $f\left( x \right)=ax,x\in \mathbb{Q},f\left( x \right)=bx,x\in \mathbb{R}\backslash \mathbb{Q}$, where $a$ and $b$ are two real numbers different from 0.  
Prove that $f$ is injective if and only if $f$ is surjective. -/
theorem calculus_52172 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
  (f : ℝ → ℝ) (h : ∀ x, Irrational x → f x = b * x)
  (h' : ∀ x, ¬Irrational x → f x = a * x) :
  Function.Injective f ↔ Function.Surjective f := by
  rw [@s1 a b, s2] <;> assumption