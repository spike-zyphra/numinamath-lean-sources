import Mathlib

/- 13. For the equation $k x^{2}-(k-1) x+1=0$ with respect to $x$,
if it has rational roots, find the integer value of $k$. -/
theorem algebra_305525 (k : ℤ):
  (∃ (x:ℚ), k * x ^ 2 - (k - 1) * x + 1 = 0) ↔ k = 0 ∨ k = 6 := by

  constructor
  · rintro ⟨x, heq⟩
    -- k = 0 case is trivial.
    by_cases hk: k = 0
    · left; exact hk
    push_neg at hk

    -- discriminant of the quadratic equation is (k-3)^2-8
    replace heq: k * (x*x) + (-(k-1))*x + 1 = 0 := by
      rw [← heq]; ring
    have hdis: discrim (k:ℚ) (-(k-1)) 1 = (k-3)^2-8 := by
      dsimp only [discrim]
      ring
    -- the equation has solution, so discriminant is square of some number.
    have: IsSquare (↑((k-3)^2-8:ℤ):ℚ) := by
      push_cast
      rw [← hdis, discrim_eq_sq_of_quadratic_eq_zero heq]
      use (2*k*x + -(k-1))
      rw [← pow_two]
    -- it's square of rational number, then it's square of some integer, say, m.
    norm_cast at this
    rcases this with ⟨m, hm⟩
    replace hm: (k-3-m)*(k-3-m + (2*m)) = 8 := by
      linarith only [hm]
    -- so their difference is even.
    have h1: Even (8 / (k-3-m) - (k-3-m)) := by
      have: k-3-m ≠ 0 := by
        rintro h
        simp [h] at hm
      rw [← hm, Int.mul_ediv_cancel_left _ this]
      simp only [add_sub_cancel_left, even_two, Even.mul_right]
    -- and they multiply to 8, so only case is 2x4 and -2 x -4
    have h2 {a:ℤ} (ha: a ∣ 8) (h: Even (8 / a - a)):
      a = -4 ∨ a = -2 ∨ a = 2 ∨ a = 4 := by
      have: |a| ∣ 8 := (abs_dvd a 8).mpr ha
      replace := Int.le_of_dvd (by norm_num) this
      rw [abs_le] at this
      clear * - ha h this
      revert ha h
      rcases this with ⟨h1, h2⟩
      decide +revert
    have h3: k-3-m ∣ 8 := Dvd.intro _ hm
    specialize h2 h3 h1

    -- try these four values
    rcases h2 with h2 | h2 | h2 | h2
    <;> rw [h2] at hm
    · -- k-3-m = -4, then k-3+m = -2, m = 1.
      replace hm: m = 1 := by linarith only [hm]
      -- therefore k = 0, but we suppose k ≠ 0.
      absurd hk
      linarith only [h2, hm]
    · -- k-3-m=-2, then we solve m = -1
      replace hm: m = -1 := by linarith only [hm]
      -- we solve k = 0, contradiciton.
      absurd hk
      linarith only [h2, hm]
    · -- k-3-m = 2, we solve m = 1
      have hm: m = 1 := by linarith only [hm]
      -- this case we solve k = 6
      right; linarith only [h2, hm]
    · -- k-3-m=4, we solve m = -1
      have hm: m = -1 := by linarith only [hm]
      -- we solve k = 6.
      right; linarith only [h2, hm]

  · -- verify k = 0 or k = 6, equation has rational root.
    rintro (rfl | rfl)
    · -- k = 0, root of x+1=0 is x=-1
      use (-1); norm_num
    · -- k = 6, 1/2, 1/3 are roots of 6x^2 - 5x+1=0
      use (1/2); norm_num