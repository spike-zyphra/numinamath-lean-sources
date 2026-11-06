import Mathlib

open Real

/- Given proposition P: ∀x∈R, log<sub>2</sub>(x<sup>2</sup>+x+a) > 0 always holds true,
and proposition Q: ∃x<sub>0</sub>∈[-2, 2],
such that 2<sup>a</sup> ≤ 2<sup>x<sub>0</sub></sup>,
if proposition P ∧ Q is true, then the range of values for the real number a is _____.-/
theorem algebra_9229 {a : ℝ} {P Q : Prop} (hp : P = ∀ x, 0 < x ^ 2 + x + a ∧ 0 < logb 2 (x ^ 2 + x + a))
    (hq : Q = ∃ x₀, x₀ ∈ Set.Icc (-2) (2 : ℝ) ∧ (2 : ℝ) ^ a ≤ 2 ^ x₀) :
    P ∧ Q ↔ a ∈ Set.Ioc (5 / 4) 2 := by
  constructor
  . rintro ⟨p, q⟩
    rw [hp] at p
    rw [hq] at q
    -- When P is a true proposition, x<sup>2</sup>+x+a > 1 always holds true,
    have (x : ℝ) : 1 < x ^ 2 + x + a := by
      have := (p x).2
      rwa [← @Real.logb_one 2, Real.logb_lt_logb_iff (by norm_num) (by norm_num) (p x).1] at this
    -- which implies x<sup>2</sup>+x+a-1 > 0 always holds true.
    have (x : ℝ) : 0 < 1 * (x * x) + 1 * x + (a - 1) := by linarith [this x]
    -- Thus, Δ = 1 - 4(a - 1) < 0, which means a > $\frac{5}{4}$.
    have := discrim_lt_zero (show (1 : ℝ) ≠ 0 by norm_num) this
    rw [discrim] at this
    have ha1 : 5 / 4 < a := by nlinarith
    -- When Q is a false proposition, ¬Q is true, i.e., ∀x∈[-2, 2], 2<sup>a</sup> ≤ 2<sup>x</sup>.
    -- Hence, a > 2, which implies Q: a ≤ 2.
    have ha2 : a ≤ 2 := by
      contrapose! q
      intro x₀ hx₀
      simp at hx₀
      rw [Real.rpow_lt_rpow_left_iff (by norm_num)]
      linarith
    -- Since proposition P ∧ Q is true, both propositions P and Q must be true.
    -- Therefore, we have the system of inequalities:
    -- $$\begin{cases} a > \frac{5}{4} \\ a ≤ 2 \end{cases}$$
    -- This simplifies to $\frac{5}{4}$ < a ≤ 2.
    constructor <;> assumption
  -- The answer is: $\boxed{(\frac{5}{4}, 2]}$.
  -- Verify that interval (5/4, 2] satisfies given condition.
  rintro ⟨ha1, ha2⟩
  rw [hp, hq]
  constructor
  . intro x
    have hxpos : 0 < x ^ 2 + x + a := by
      rw [show x ^ 2 + x + a = (x + 1 / 2) ^ 2 + (a - 1 / 4) by ring]
      have : 0 ≤ (x + 1 / 2) ^ 2 := sq_nonneg _
      have : 0 < a - 1 / 4 := by linarith
      linarith
    constructor
    . exact hxpos
    rw [← @Real.logb_one 2, Real.logb_lt_logb_iff (by norm_num) (by norm_num) hxpos]
    suffices 0 < x ^ 2 + x + a - 1 by linarith
    rw [show x ^ 2 + x + a - 1 = (x + 1 / 2) ^ 2 + (a - 5 / 4) by ring]
    have : 0 ≤ (x + 1 / 2) ^ 2 := sq_nonneg _
    have : 0 < a - 5 / 4 := by linarith
    linarith
  use 2
  constructor
  . simp
  rwa [Real.rpow_le_rpow_left_iff (by norm_num)]
