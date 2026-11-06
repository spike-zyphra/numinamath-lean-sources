import Mathlib

/- Find all pairs $(x, y)$ of integers which satisfy the equation

$$
(x+y)^{2}\left(x^{2}+y^{2}\right)=2009^{2}
$$ -/
theorem number_theory_605265 :
    {(x, y) : ℤ × ℤ | (x + y) ^ 2 * (x ^ 2 + y ^ 2) = 2009 ^ 2} = {(-40, -9), (-9, -40), (9, 40), (40, 9)} := by
  -- Simplify the goal into two parts.
  rw [Set.ext_iff]
  intro (x, y)
  simp
  apply Iff.intro
  . -- First show that the equation implies (x, y) = (-40, -9), (-9, -40), (9, 40) or (40, 9).
    intro h₀
    -- Let s = x + y and p = xy.
    let s := x + y
    let p := x * y
    rw [show x + y = s by rfl, show x ^ 2 + y ^ 2 = s ^ 2 - 2 * p by ring_nf] at h₀
    -- We have s ∣ 2009 because s² divides 2009².
    have h₁ : s ^ 2 ∣ 2009 ^ 2 := by
      norm_num
      rw [<-h₀]
      apply dvd_mul_right
    rw [Int.pow_dvd_pow_iff (by norm_num)] at h₁
    -- Let t = |s|.
    let t := s.natAbs
    rw [<-Int.natAbs_dvd, show s.natAbs = t by rfl] at h₁
    norm_cast at h₁
    -- Analyze the possibilities of t by t ∣ 2009.
    replace h₁ : t ∣ 2009 ∧ 2009 ≠ 0 := by
      tauto
    rw [<-Nat.mem_divisors] at h₁
    -- Use the computer to find the factors of 2009 (native_decide is necessary).
    rw [show Nat.divisors 2009 = {1, 7, 41, 49, 287, 2009} by native_decide] at h₁
    simp at h₁
    -- Substitute t into the equation h₀.
    rw [show s ^ 2 = t ^ 2 by rw [Int.natAbs_sq]] at h₀
    -- Get the quadratic relation that x satisfies in terms of s and p.
    have h₂ : x ^ 2 - s * x + p = 0 := by
      ring_nf
    replace h₂ : (2 * x - s) ^ 2 = s ^ 2 - 4 * p := by
      linarith only [h₂]
    -- Consider the cases t = 1, 7, 41, 49, 287, 2009 resepctively.
    rcases h₁ with (h₁ | h₁ | h₁ | h₁ | h₁ | h₁)
    . -- Case s = ±1.
      simp [h₁] at h₀
      simp [t] at h₁
      rw [Int.natAbs_eq_iff] at h₁
      rw [show p = -2018040 by linarith only [h₀]] at h₂
      norm_num at h₂
      rcases h₁ with (h₁ | h₁)
      . rw [h₁] at h₂
        -- Now we can derive the absurd statement that 8072161 is a square.
        let r := |2 * x - 1|
        -- Let r be the non-negative solution of r² = 8072161.
        simp at h₂
        rw [<-sq_abs, show |2 * x - 1| = r by rfl] at h₂
        -- Now r is defined in such a way that 0 ≤ r.
        have ht : 0 ≤ r := by
          simp [r]
        -- Contradiction is derived as 2841 < r < 2842.
        linarith only [show 2841 < r by nlinarith only [h₂, ht], show r < 2842 by nlinarith only [h₂, ht]]
      . rw [h₁] at h₂
        -- Now we can derive the absurd statement that 8072161 is a square.
        let r := |2 * x + 1|
        -- Let r be the non-negative solution of r² = 8072161.
        simp at h₂
        rw [<-sq_abs, show |2 * x + 1| = r by rfl] at h₂
        -- Now r is defined in such a way that 0 ≤ r.
        have ht : 0 ≤ r := by
          simp [r]
        -- Contradiction is derived as 2841 < r < 2842.
        linarith only [show 2841 < r by nlinarith only [h₂, ht], show r < 2842 by nlinarith only [h₂, ht]]
    . -- Case s = ±7.
      simp [h₁] at h₀
      simp [t] at h₁
      rw [Int.natAbs_eq_iff] at h₁
      rw [show p = -41160 by linarith only [h₀]] at h₂
      norm_num at h₂
      rcases h₁ with (h₁ | h₁)
      . rw [h₁] at h₂
        -- Now we can derive the absurd statement that 164689 is a square.
        let r := |2 * x - 7|
        -- Let r be the non-negative solution of r² = 164689.
        simp at h₂
        rw [<-sq_abs, show |2 * x - 7| = r by rfl] at h₂
        -- Now r is defined in such a way that 0 ≤ r.
        have ht : 0 ≤ r := by
          simp [r]
        -- Contradiction is derived as 405 < r < 406.
        linarith only [show 405 < r by nlinarith only [h₂, ht], show r < 406 by nlinarith only [h₂, ht]]
      . rw [h₁] at h₂
        -- Now we can derive the absurd statement that 164689 is a square.
        let r := |2 * x + 7|
        -- Let r be the non-negative solution of r² = 164689.
        rw [sub_neg_eq_add] at h₂
        simp at h₂
        rw [<-sq_abs, show |2 * x + 7| = r by simp [r]] at h₂
        -- Now r is defined in such a way that 0 ≤ r.
        have ht : 0 ≤ r := by
          simp [r]
        -- Contradiction is derived as 405 < r < 406.
        linarith only [show 405 < r by nlinarith only [h₂, ht], show r < 406 by nlinarith only [h₂, ht]]
    . -- Case s = ±41.
      simp [h₁] at h₀
      simp [t] at h₁
      rw [Int.natAbs_eq_iff] at h₁
      rw [show p = -360 by linarith only [h₀]] at h₂
      norm_num at h₂
      rcases h₁ with (h₁ | h₁)
      . rw [h₁] at h₂
        -- Now we can derive the absurd statement that 3121 is a square.
        let r := |2 * x - 41|
        -- Let r be the non-negative solution of r² = 3121.
        simp at h₂
        rw [<-sq_abs, show |2 * x - 41| = r by simp [r]] at h₂
        -- Now r is defined in such a way that 0 ≤ r.
        have ht : 0 ≤ r := by
          simp [r]
        -- Contradiction is derived as 55 < r < 56.
        linarith only [show 55 < r by nlinarith only [h₂, ht], show r < 56 by nlinarith only [h₂, ht]]
      . rw [h₁] at h₂
        -- Now we can derive the absurd statement that 3121 is a square.
        let r := |2 * x + 41|
        rw [sub_neg_eq_add] at h₂
        -- Let r be the non-negative solution of r² = 3121.
        simp at h₂
        rw [<-sq_abs, show |2 * x + 41| = r by simp [r]] at h₂
        -- Now r is defined in such a way that 0 ≤ r.
        have ht : 0 ≤ r := by
          simp [r]
        -- Contradiction is derived as 55 < r < 56.
        linarith only [show 55 < r by nlinarith only [h₂, ht], show r < 56 by nlinarith only [h₂, ht]]
    . -- Case s = ±49.
      simp [h₁] at h₀
      simp [t] at h₁
      rw [Int.natAbs_eq_iff] at h₁
      rw [show p = 360 by linarith only [h₀]] at h₂
      norm_num at h₂
      rcases h₁ with (h₁ | h₁)
      . rw [h₁] at h₂
        -- We have (2x - 49)² = 31².
        simp at h₂
        rw [show (961 : ℤ) = 31 ^ 2 by norm_num] at h₂
        rw [sq_eq_sq_iff_eq_or_eq_neg] at h₂
        -- Now we have two cases: 2x - 49 = 31 or 2x - 49 = -31.
        rcases h₂ with (h₂ | h₂)
        . -- Case 2x - 49 = 31.
          right
          right
          right
          -- Corresponding to the solution (x, y) = (40, 9).
          simp [s] at h₁
          exact ⟨by linarith, by linarith⟩
        . -- Case 2x - 49 = -31.
          right
          right
          left
          -- Corresponding to the solution (x, y) = (9, 40).
          simp [s] at h₁
          exact ⟨by linarith, by linarith⟩
      . rw [h₁] at h₂
        -- We have (2x + 49)² = 31².
        rw [sub_neg_eq_add] at h₂
        simp at h₂
        rw [show (961 : ℤ) = 31 ^ 2 by norm_num] at h₂
        rw [sq_eq_sq_iff_eq_or_eq_neg] at h₂
        -- Now we have two cases: 2x + 49 = 31 or 2x + 49 = -31.
        rcases h₂ with (h₂ | h₂)
        . -- Case 2x + 49 = 31.
          right
          left
          -- Corresponding to the solution (x, y) = (-9, -40).
          simp only [s] at h₁
          norm_num at h₁
          exact ⟨by linarith, by linarith⟩
        . -- Case 2x + 49 = -31.
          left
          -- Corresponding to the solution (x, y) = (-40, -9).
          simp only [s] at h₁
          norm_num at h₁
          exact ⟨by linarith, by linarith⟩
    . -- Case s = ±287.
      simp [h₁] at h₀
      simp [t] at h₁
      rw [Int.natAbs_eq_iff] at h₁
      rw [show p = 41160 by linarith only [h₀]] at h₂
      norm_num at h₂
      rcases h₁ with (h₁ | h₁)
      . rw [h₁] at h₂
        -- Derive the absurd statement that -82271 is a square.
        simp at h₂
        linarith only [h₂, sq_nonneg (2 * x - 287)]
      . rw [h₁] at h₂
        -- Derive the absurd statement that -82271 is a square.
        rw [sub_neg_eq_add] at h₂
        simp at h₂
        linarith only [h₂, sq_nonneg (2 * x + 287)]
    . -- Case s = ±2009.
      simp [h₁] at h₀
      simp [t] at h₁
      rw [Int.natAbs_eq_iff] at h₁
      rw [show p = 2018040 by linarith only [h₀]] at h₂
      norm_num at h₂
      rcases h₁ with (h₁ | h₁)
      . rw [h₁] at h₂
        -- Derive the absurd statement that -4036079 is a square.
        simp at h₂
        linarith only [h₂, sq_nonneg (2 * x - 2009)]
      . rw [h₁] at h₂
        -- Derive the absurd statement that -4036079 is a square.
        rw [sub_neg_eq_add] at h₂
        simp at h₂
        linarith only [h₂, sq_nonneg (2 * x + 2009)]
  . -- Show that the four solutions indeed satisfy the given equation.
    rintro (⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩)
    all_goals
      rw [hx, hy]
      norm_num
  