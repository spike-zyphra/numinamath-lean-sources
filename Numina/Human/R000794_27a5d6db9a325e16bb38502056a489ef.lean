import Mathlib

open Real Set
open scoped Real
/- Let $x$ be an angle such that $\tan x = \frac{a}{b}$ and $\tan 2x = \frac{b}{a + b}.$  Then the least positive value of $x$ equals $\tan^{-1} k.$  Compute $k.$ -/
theorem calculus_15459 {a b k: ℝ} (ha : a ≠ -b) (bnz: b ≠ 0)
  (h: IsLeast {x:ℝ | 0 < x ∧ tan x = a / b ∧ tan (2 * x) = b / (a + b)}
    (arctan k)): k = 1/3  := by
  rw [IsLeast, lowerBounds] at h; simp at h
  -- a+b is at denominator, cannot be zero. therefore a/b+1 ≠ 0
  have hnz1: a/b + 1 ≠ 0 := by
      by_contra! hc
      have ht1: a/b = -1 := by linarith [hc]
      have ht2: a = -b := by
        have: -b = b*-1 := by ring
        rw [this, ← ht1]
        by_cases hb: b = 0
        · rw [hb] at hc; simp at hc
        · field_simp [hb]
      contradiction
  -- and we can verify a = b does not satisfy. therefore a ≠ b
  have aneb : a ≠ b := by
    by_contra! hc; rw[hc] at h
    have keq1: k = 1 := by
      have := h.left.right.left
      rw [this]; exact (div_eq_one_iff_eq bnz).mpr rfl
    have con := h.left.right
    rw [keq1] at con
    have hh1: b/(b+b) = 1/2 := by
      field_simp [bnz]; ring
    have hh2: 2* arctan 1 = π/2 := by
      simp; ring
    rw [hh1, hh2] at con; simp at con
  -- notice that tan2x = b/(a+b) = 1/(a/b+1) = 1/(tanx + 1)
  have h1: ∀x:ℝ, tan x = a / b ∧ tan (2 * x) = b / (a + b) →
    tan (2*x) = 1 / (tan x + 1) := by
    intro x ⟨htan1, htan2⟩
    rw [htan2, htan1]
    have hh1: a+b ≠ 0 := by
      by_contra! hc
      have: a = -b := by linarith [hc]
      contradiction
    field_simp [hnz1, hh1]
  -- recall that tan2x = 2tanx / (1-(tanx)^2), substitute, and we have following equation.
  have h2: ∀x:ℝ, tan x = a / b ∧ tan (2 * x) = b / (a + b) →
    2 * (tan x) * (tan x + 1) + (tan x)^2 - 1 = 0 := by
    intro x h'
    have h1' := h1 x h'
    rw [Real.tan_two_mul] at h1'
    have hh2: tan x + 1 ≠ 0 := by
      rw [h'.left]; apply hnz1
    have hh3: tan x - 1 ≠ 0 := by
      by_contra! hc
      have tt1: tan x = 1 := by linarith [hc]
      have tt2: a = b := by
        rw [h'.left] at tt1
        have: a = a/b * b := by
          symm; exact div_mul_cancel₀ a bnz
        rw [this, tt1]; simp
      contradiction
    have hh4: 2*tan x = (2*tan x) / (1- (tan x)^2) * (1- (tan x)^2) := by
      have: 1- (tan x)^2 ≠ 0 := by
        have tt1: 1 - (tan x)^2 = - ((tan x + 1) * (tan x - 1)) := by ring
        have tt2: (tan x + 1) * (tan x - 1) ≠ 0 := by
          exact mul_ne_zero hh2 hh3
        rw [tt1]; exact neg_ne_zero.mpr tt2
      symm
      exact div_mul_cancel₀ (2 * tan x) this
    rw [hh4, h1']
    rw [mul_comm _ (tan x + 1), ← mul_assoc, mul_one_div_cancel hh2]
    ring
  -- thus we have 2tanx(tanx +1) + (tanx)^2-1 =0. or, (tanx)^2-1 = (tanx+1)(tanx-1), then (tanx+1)(2tanx+tanx-1)=0. that is (tan x + 1)(3tan x - 1) = 0
  have h3: ∀x:ℝ, tan x = a / b ∧ tan (2 * x) = b / (a + b) →
    (tan x + 1)*(3*tan x - 1) = 0 := by
    intro x h'
    have h2' := h2 x h'
    have: (tan x + 1)*(3*tan x - 1) =
      2*tan x * (tan x + 1) + (tan x)^2 - 1 := by ring
    rw [this, h2']
  -- thus we solve tan x = -1 or tan x = 1/3
  have h4: ∀x:ℝ, tan x = a / b ∧ tan (2 * x) = b / (a + b) →
    tan x = -1 ∨ tan x = 1/3 := by
    intro x h'
    rcases (mul_eq_zero.mp (h3 x h')) with hl | hr
    · left; linarith [hl]
    · right; linarith [hr]
  -- k = tan x, so k = -1 or 1/3
  have keq: k = -1 ∨ k = 1/3 := by
    have hh1 := h.left.right
    have hh2: k = tan (arctan k) := by simp
    have: tan (arctan k) = -1 ∨ tan (arctan k) = 1/3 := by
      nth_rw 1 [hh2] at hh1
      apply h4 (arctan k) hh1
    rw [hh2]
    exact this
  -- and we require tan x to be positive, so k can only be 1/3
  have kpos: 0 < k := by
    have hh1 := h.left.left
    simp at hh1
    by_contra! knonpos
    have hh2: k = tan (arctan k) := by simp
    rw [hh2] at knonpos
    have hh3: arctan k ≤ 0 := by
      rw [← tan_zero] at knonpos
      have: arctan k ∈ (Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
        arctan_mem_Ioo k
      rw [← arctan_zero]
      have arctan_mono := StrictMono.monotone arctan_strictMono
      apply arctan_mono
      rw [hh2, ← tan_zero]; exact knonpos
    linarith [hh1, hh3]
  rcases keq with kneg | kpos
  · linarith [kpos, kneg]
  · exact kpos