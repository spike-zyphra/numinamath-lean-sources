import Mathlib

-- we show that f is injective
lemma f_is_injective (f : ℝ → ℝ)
  (h: ∀ x y, f (x ^ 2 + f y) = y + (f x) ^ 2): ∀ x y, x ≠ y → f x ≠ f y := by
  intro x y ne
  by_contra! o
  have h1:= h 0 x
  simp at h1
  have h2:= h 0 y
  simp at h2
  simp [o] at h1
  rw [h1] at h2
  absurd ne
  linarith

-- then we prove that f is surjective
lemma f_is_surjective (f : ℝ → ℝ)
  (h: ∀ x y, f (x ^ 2 + f y) = y + (f x) ^ 2): ∀ z, ∃ x, f x = z := by
  intro z
  specialize h 0 (z - (f 0) ^ 2)
  simp at h
  use f (z - (f 0) ^ 2)


  /- 6. (IND 2) ${ }^{\mathrm{IMO} 2}$
Find all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ such that
$$ f\left(x^{2}+f(y)\right)=y+f(x)^{2} \quad \text { for all } x, y \text { in } \mathbb{R} $$ -/

theorem algebra_24446 (f : ℝ → ℝ) :
  (∀ x y, f (x ^ 2 + f y) = y + (f x) ^ 2) ↔ ∀ x, f x = x := by

  constructor

  -- the forward direction
  .
    intro h

    -- we first show that f 0 = 0
    have h0: f 0 = 0 := by
      have hz:= f_is_surjective f h 0
      obtain ⟨z, hz⟩ := hz
      suffices z = 0 by
        simp [this] at hz
        exact hz
      by_contra! o
      have h1:= h z 0
      have h2:= h (-z) 0
      simp at h1 h2
      rw [h1] at h2
      simp [hz] at h2
      symm at h2
      simp at h2
      rw [← h2] at hz
      have j:= f_is_injective f h z (-z)
      have k: z ≠ -z := by
        by_contra! s
        absurd o
        linarith
      simp [k] at j
      tauto

    -- then we show that f(-x) = -f(x)
    have h1: ∀ x, f (-x) = -f x := by
      intro x
      have f1:= h x 0
      have f2:= h (-x) 0
      simp at f2
      rw [f2] at f1
      replace f1: (f x - f (-x)) * (f x + f (-x)) = 0 := by
        nlinarith
      simp at f1
      by_cases j: x = 0
      .
        simp [j]
        linarith
      .
        have k:= f_is_injective f h x (-x)
        have l: x ≠ -x := by
          by_contra! s
          absurd j
          linarith
        simp [l] at k
        rcases f1 with f1 | f1
        .
          absurd k
          linarith
        .
          linarith

    have h2: ∀ x, f (x ^ 2) = (f x) ^ 2 := by
      intro x
      specialize h x 0
      simp [h0] at h
      tauto

    -- then we show that f preserves sign
    have fp: ∀ x, 0 < x → 0 < f x := by
      intro x hx
      specialize h2 √x
      have o: √x ^ 2 = x := by
        symm
        rw [← Real.sqrt_eq_iff_eq_sq]
        linarith
        apply Real.sqrt_nonneg
      simp [o] at h2
      rw [h2]
      suffices (f √x) ^ 2 ≠ 0 by
        have u:= sq_nonneg (f √x)
        by_contra! s
        absurd this
        linarith
      by_contra! s
      simp at s
      have k:= f_is_injective f h √x 0
      have l: √x ≠ 0 := by
        by_contra! t
        rw [Real.sqrt_eq_zero] at t
        linarith
        linarith
      simp [l] at k
      simp [s, h0] at k

    have fn: ∀ x, x < 0 → f x < 0 := by
      intro x hx
      specialize h1 x
      suffices 0 < f (- x) by linarith
      specialize fp (-x) (by linarith)
      tauto

    -- use the above fact, we can finally show that f x = x
    have h3: ∀ x, 0 < x → f x = x := by
      intro x hx
      have g:= h √x (-x)
      have o: √x ^ 2 = x := by
        symm
        rw [← Real.sqrt_eq_iff_eq_sq]
        linarith
        apply Real.sqrt_nonneg
      have o2: (f √x) ^ 2 = f x := by
        specialize h2 √x
        rw [o] at h2
        tauto
      simp [o] at g
      clear o
      have s1:= h1 x
      simp [s1, o2] at g
      rw [show -x + f x = - (x + -f x) by abel] at g
      set t:= x + -f x

      -- by the sign argument, we obtain that t = 0
      have vt: t = 0 := by
        by_contra! ne
        by_cases l: 0 < t
        .
          specialize fp t l
          linarith
        .
          simp at l
          replace l: t < 0 := by
            by_contra! s
            absurd ne
            linarith
          specialize fn t l
          linarith

      simp [t] at vt
      linarith

    intro x
    by_cases u: 0 < x
    .
      exact h3 x u
    .
      simp at u
      by_cases v: x = 0
      .
        simp [v, h0]
      .
        replace u: x < 0 := by
          by_contra! s
          absurd v
          linarith
        specialize h3 (-x) (by linarith)
        specialize h1 x
        linarith


  -- the backward direction
  .
    intro h
    intro x y
    have fx:= h x
    have fy:= h y
    have g:= h (x ^ 2 + f y)
    simp [fx, fy]
    simp [fy] at g
    simp [g]
    abel
