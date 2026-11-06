import Mathlib

open Real

/- Example 3 Solve the inequality $(\lg x+3)^{7}+\lg ^{7} x+\lg x^{2}+3 \geqslant 0$.

Translate the text above into English, please keep the original text's line breaks and format, and output the translation result directly. -/
theorem inequalities_292001 (x : ℝ) (hx : 0 < x) :
    (logb 10 x + 3)^7 + logb 10 x^7 + logb 10 (x^2) + 3 ≥ 0 ↔
    10^(-3/2 : ℝ) ≤ x := by
  -- define f(t) = t ^ 7 + t
  set f : ℝ → ℝ := fun t => t ^ 7 + t
  -- f(t) is strictly monotone
  have hf_mono : StrictMono f := by
    apply StrictMono.add _ (by exact fun ⦃a b⦄ a ↦ a)
    exact Odd.strictMono_pow (by decide)
  -- we have
  -- (lg x + 3)^7 + lg x^7 + lg (x^2) + 3
  -- = (lg x + 3)^7 + (lg x + 3) + (lg x^7 + lg x)
  -- = f(lg x + 3) + f(lg x)
  -- = f(lg x + 3) - f(-lg x)
  -- we continue as follows
  -- f(lg x + 3) ≥ f(-lg x) ↔ -lg x ≤ lg x + 3 (because f is strictly monotone)
  --                        ↔ -3 / 2 ≤ lg x
  --                        ↔ 10 ^ (-3 / 2) ≤ x
  calc
    (logb 10 x + 3)^7 + logb 10 x^7 + logb 10 (x^2) + 3 ≥ 0 ↔ f (logb 10 x + 3) ≥ f (-logb 10 x) := by
        simp [logb_pow, f]
        symm
        rw [←sub_nonneg]
        ring_nf
    _ ↔ -logb 10 x ≤ logb 10 x + 3 := by rw [ge_iff_le, hf_mono.le_iff_le]
    _ ↔ -3/2 ≤ logb 10 x := by constructor <;> intro h <;> linarith
    _ ↔ 10^(-3/2 : ℝ) ≤ x := by rw [Real.le_logb_iff_rpow_le (by norm_num) hx]