import Mathlib

/-
7. Find all integers $a, b, c, d$ satisfying the following relations:

(i) $1 \leq a \leq b \leq c \leq d$;

(ii) $a b+c d=a+b+c+d+3$.
 -/
theorem algebra_122634 (a b c d : ℤ) : 1 ≤ a ∧ a ≤ b ∧ b ≤ c ∧ c ≤ d ∧
    a * b + c * d = a + b + c + d + 3 ↔
    (a, b, c, d) = (1, 1, 2, 6) ∨ (a, b, c, d) = (1, 2, 2, 6) ∨
    (a, b, c, d) = (2, 2, 2, 5) ∨ (a, b, c, d) = (2, 2, 3, 3) := by
  constructor <;> rintro h
  -- from equation to solutions
  . obtain ⟨ha, hab, hbc, hcd, h⟩ := h
    -- write as expression of a-1, b-1, c-1, d-1
    replace h : (a-1) * (b-1) + (c-1) * (d-1) = 5 := by linarith
    -- if a-1 is too large than others are alos large and equation can't be true
    have : a ≤ 2 := by
      by_contra ha'
      replace ha' : 2 ≤ a - 1 := by omega
      have : 2 * 2 + 2 * 2 ≤ (a-1) * (b-1) + (c-1) * (d-1) := by
        gcongr <;> linarith
      linarith
    -- define c', d' as we'll use them for primality facts
    let c' := (c-1).toNat
    let d' := (d-1).toNat
    -- a is 1 or 2
    interval_cases a <;> simp at h ⊢
      -- since c' * d' = 5, c' = 1 or 5
    . have h' : c' * d' = 5 := by
        zify
        simp only [c', d']
        rwa [Int.toNat_of_nonneg, Int.toNat_of_nonneg]
        all_goals omega
      replace h' : c' = 1 ∨ c' = 5 := by
        refine Nat.dvd_prime ?_ |>.mp ?_
        . norm_num
        . use d'; linarith
      -- so (c-1) = 1 or 5
      simp [c'] at h'
      zify at h'
      rw [Int.toNat_of_nonneg (by omega)] at h'
      obtain h' | h' := h' <;> simp [h']
        -- from c = 2, we get bounds 1 and 2 for b, from thise we get two solutions
      . rw [h'] at h hbc
        simp at h
        simp [show d = 6 by linarith]
        interval_cases b <;> simp
        -- c = 6 is impossible as then d becomes less than c
      . rw [h'] at h
        simp at h
        linarith
      -- for a = 2, we first have b ≤ 2, otherwise others get too big
    . have hb : b ≤ 2 := by
        by_contra hb
        replace hb : 2 ≤ (b-1) := by omega
        have : 2 + 2 * 2 ≤ (b-1) + (c-1) * (d-1) := by
          gcongr <;> linarith
        linarith
      -- so b = 2
      replace hb : b = 2 := by linarith
      simp [hb]
      rw [hb] at h
      -- now c must be within 1 or 5
      replace h : (c-1) * (d-1) = 4 := by linarith
      have hc₁ : 1 ≤ c := by omega
      have hc₂ : c ≤ 5 := by
        suffices c-1 ≤ 4 by linarith
        apply Int.le_of_dvd (by norm_num)
        use (d-1)
        linarith
      -- we try out all cases
      interval_cases c
      any_goals simp
      any_goals linarith
    -- for checking solutions just plug in values and calculate
  . obtain h | h | h | h := h
    all_goals (
      simp at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      norm_num
    )