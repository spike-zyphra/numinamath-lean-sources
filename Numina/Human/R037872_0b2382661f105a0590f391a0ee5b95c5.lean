import Mathlib

open Real

/- Let

$$
f(r)=\frac{a^{\frac{1}{2}+r}+b^{\frac{1}{2}+r}}{a^{\frac{1}{2}-r}+b^{\frac{1}{2}-r}}
$$

Prove that

$$
\begin{aligned}
& \text { a) } f(r) \leq(a b)^{r}, \quad \text { if } \quad r>0
\end{aligned}
$$

(For the latter problem, see the article "On Weighted Arithmetic Means" in the previous issue of our journal.)

 -/
theorem inequalities_249244 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (f : ℝ → ℝ) (hf : f = fun r => (a ^ ((1 / 2) + r) + b ^ ((1 / 2) + r)) /
    (a ^ ((1 / 2) - r) + b ^ ((1 / 2) - r))) :
    ∀ r, 0 < r → f r ≥ (a * b) ^ r := by
  intro r hr
  -- First of all, we must note that $a&gt;0$ and $b&gt;0$, because otherwise the general expressions $a^{\frac{1}{2}+r}$, etc., might not make sense.
  -- a) It is enough to prove the inequality that arises from the inequality to be proven, $f(r) \leq (a b)^{r}$, when we multiply it by $\left(a^{\frac{1}{2}-r}+b^{\frac{1}{2}-r}\right)$, which is necessarily positive.
  -- $$ a^{\frac{1}{2}+r}+b^{\frac{1}{2}+r} \leq a^{\frac{1}{2}} b^{r}+a^{r} b^{\frac{1}{2}} $$
  suffices h : a ^ (1 / 2 + r) + b ^ (1 / 2 + r) ≥ a ^ (1 / 2 : ℝ) * b ^ r + a ^ r * b ^ (1 / 2 : ℝ)
  · calc
      f r = (a ^ (1 / 2 + r) + b ^ (1 / 2 + r)) / (a ^ (1 / 2 - r) + b ^ (1 / 2 - r)) := by rw [hf]
      _ ≥ (a ^ (1 / 2 : ℝ) * b ^ r + a ^ r * b ^ (1 / 2 : ℝ)) / (a ^ (1 / 2 - r) + b ^ (1 / 2 - r)) := by rel [h]
      _ = (a * b) ^ r := by
        rw [rpow_sub ha, rpow_sub hb]
        field_simp
        ring_nf
        rw [mul_rpow (le_of_lt ha) (le_of_lt hb)]
        ring
  · -- or equivalently,
    -- $$ a^{\frac{1}{2}+r}+b^{\frac{1}{2}+r}-a^{\frac{1}{2}} b^{r}-a^{r} b^{\frac{1}{2}} \leq 0 $$
    -- which can also be written as:
    -- $$ \left(a^{\frac{1}{2}}-b^{\frac{1}{2}}\right)\left(a^{r}-b^{r}\right) \leq 0 $$
    suffices h : (a ^ (1 / 2 : ℝ) - b ^ (1 / 2 : ℝ)) * (a ^ r - b ^ r) ≥ 0
    · rw [sub_mul, mul_sub, mul_sub] at h
      rw [rpow_add, rpow_add]
      calc
        _ = a ^ (1 / 2 : ℝ) * a ^ r - a ^ (1 / 2 : ℝ) * b ^ r - (b ^ (1 / 2 : ℝ) * a ^ r - b ^ (1 / 2 : ℝ) * b ^ r) + (a ^ (1 / 2 : ℝ) * b ^ r + b ^ (1 / 2 : ℝ) * a ^ r) := by ring
        _ ≥ 0 + (a ^ (1 / 2 : ℝ) * b ^ r + b ^ (1 / 2 : ℝ) * a ^ r) := by rel [h]
        _ = _ := by ring
      exact hb
      exact ha
    · -- This inequality is true because
      -- if $a^{\frac{1}{2}} \geq b^{\frac{1}{2}}$, then $a^{r} \geq b^{r}$,
      by_cases h : a ≥ b
      · apply mul_nonneg
        · simp
          apply rpow_le_rpow
          · exact le_of_lt hb
          · exact h
          · norm_num
        · simp
          apply rpow_le_rpow
          · exact le_of_lt hb
          · exact h
          · exact le_of_lt hr
      -- and if $a^{\frac{1}{2}} \leq b^{\frac{1}{2}}$, then $a^{r} \leq b^{r}$, due to $r&gt;0$ causing the two factors to have the same sign.
      · simp at h
        apply mul_nonneg_of_nonpos_of_nonpos
        · simp
          apply rpow_le_rpow
          · exact le_of_lt ha
          · exact le_of_lt h
          · norm_num
        · simp
          apply rpow_le_rpow
          · exact le_of_lt ha
          · exact le_of_lt h
          · exact le_of_lt hr
