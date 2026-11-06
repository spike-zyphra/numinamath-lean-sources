import Mathlib

/- The maximum and minimum values of the function $y=x^2-6x+8$ on the interval $[2, 6]$ are     and     , respectively. -/
theorem algebra_9409 (f : ℝ → ℝ) (hf : f = fun x => x ^ 2 - 6 * x + 8) : IsGreatest (Set.image f (Set.Icc 2 6)) 8 ∧ IsLeast (Set.image f (Set.Icc 2 6)) (-1) := by
-- notice that x^2-6x+8=(x-3)^-1
have feq: f = fun x => (x-3)^2-1 := by
  rw [hf]
  ext x
  ring
-- (x-3)^2 reaches minimum at x=3, and is symmetric of x=3. so on interval [2,6], its maximum is at x=6, and f(6)=8.
have fG: IsGreatest (f '' Set.Icc 2 6) 8 := by
  rw [IsGreatest]
  have h1: 8 ∈ f '' Set.Icc 2 6 := by
    simp
    -- reaches maximum at x-6, so use 6.
    use (6:ℝ)
    have hl: ((2:ℝ) ≤ 6 ∧ (6:ℝ) ≤ 6) := by
      have hll: (2:ℝ) ≤ 6 := by norm_num
      have hrr: (6:ℝ) ≤ 6 := by norm_num
      exact ⟨hll,hrr⟩
    have hr: f 6 = 8 := by
      rw [hf]
      simp
      ring
    exact ⟨hl, hr⟩
  have h2: 8 ∈ upperBounds (f '' Set.Icc 2 6) := by
    intro y hy
    simp at hy
    by_contra! yne
    rcases hy with ⟨x, ⟨xlower,xupper⟩, hx⟩
    have ht1: |x-3| ≤ |3| := by
      rw [abs_le]
      have: |(3:ℝ)| = 3 := by simp
      have xl: -|3| ≤ x - 3 := by
        linarith [xlower]
      have xr:  x - 3 ≤ |3| := by linarith [xupper]
      exact ⟨xl, xr⟩
    have ht2: (x-3)^2 ≤ 3^2 := sq_le_sq.mpr ht1
    have ht3: f x ≤ 8 := by
      rw [feq]
      simp
      linarith
    rw [hx] at ht3
    linarith
  exact ⟨h1,h2⟩
-- obviously, when x=3, (x-3)^2=0, and f(x) reaches minimum. f(3)=-1.
have fL: IsLeast (f '' Set.Icc 2 6) (-1) := by
  rw [IsLeast]
  have h1: -1 ∈ f '' Set.Icc 2 6 := by
    simp
    use (3:ℝ)
    have hl: ((2:ℝ) ≤ 3 ∧ (3:ℝ) ≤ 6) := by
      have hll: (2:ℝ) ≤ 3 := by norm_num
      have hrr: (3:ℝ) ≤ 6 := by norm_num
      exact ⟨hll,hrr⟩
    have hr: f 3 = -1 := by
      rw [hf]
      simp
      ring
    exact ⟨hl,hr⟩
  have h2: -1 ∈ lowerBounds (f '' Set.Icc 2 6) := by
    intro y hy
    simp at hy
    by_contra! yne
    rcases hy with ⟨x, ⟨xlower,xupper⟩, hx⟩
    have hcc: y ≥ -1 := by
      rw [← hx, feq]
      simp [sq_nonneg (x - 3)]
    linarith
  exact ⟨h1,h2⟩
exact ⟨fG,fL⟩
