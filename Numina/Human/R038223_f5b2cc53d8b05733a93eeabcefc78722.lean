import Mathlib

open Topology Filter Real

/- 13. Given the sequence $a_{1}=1, a_{n}=1-\frac{1}{4 a_{n-1}}$, and $b_{n}=\frac{2}{2 a_{n}-1}$.
(1) Prove: For $n \geqslant 1$, it always holds that $\frac{1}{2} < a_{n} \leq slant 1$;
(2) Find the general term formula for the sequence $\left\{b_{n}\right\}$;
(3) Find the value of $\lim _{n \rightarrow+\infty} \frac{a_{n}}{b_{n}}$. -/
theorem algebra_287838 {a b : ℕ → ℝ}
    (ha1 : a 1 = 1)
    (han : ∀ n ≥ 2, a n = 1 - 1 / (4 * a (n - 1)))
    (hb : ∀ n ≥ 1, b n = 2 / (2 * a n - 1)) :
    (∀ n ≥ 1, 1 / 2 < a n ∧ a n ≤ 1) ∧
    (∀ n ≥ 1, b n = 2 * n) ∧
    (Tendsto (λ n => a n / b n) atTop (𝓝 0)) := by
  -- Show that 1 / 2 < a(n) ≤ 1 for all 1 ≤ n
  have ha {n} (hn : 1 ≤ n) : 1 / 2 < a n ∧ a n ≤ 1 := by
    rw [show n = (n - 1) + 1 by omega]
    -- It is more convenient to prove everything for a(m + 1) for 0 ≤ m.
    generalize n - 1 = m
    -- Proof by induction.
    induction m with
    -- a(1) = 1, 1 / 2 < 1 ≤ 1.
    | zero => norm_num [ha1]
    | succ m ih =>
      -- Assume that 1 / 2 < a(m + 1) ≤ 1 and show that
      -- 1 / 2 < a(m + 2) ≤ 1.
      -- We have a(m + 2) = 1 - 1 / (4 * a(m + 1)).
      rw [han (m + 1 + 1) (by linarith), show m + 1 + 1 - 1 = m + 1 by omega]
      -- It is enough to show that 0 ≤ 1 / (4 * a(m + 1)) < 1 / 2.
      rw [show ∀ x : ℝ, 1 / 2 < 1 - x ↔ x < 1 / 2 by intros; constructor <;> (intros; linarith)]
      rw [show ∀ x : ℝ, 1 - x ≤ 1 ↔ 0 ≤ x by intros; constructor <;> (intros; linarith)]
      have h0 : 0 < a (m + 1) := by linarith
      -- 0 ≤ 1 / (4 * a(m + 1)) because 1 / 2 < a(m + 1).
      refine ⟨?_, by positivity⟩
      simp_rw [one_div]
      -- 1 / (4 * a(m + 1)) < 1 / 2 is equivalent to 2 < 4 * a(m + 1).
      rw [inv_lt_inv₀ (by linarith) (by norm_num)]
      -- 1 / 2 < a(m + 1) implies that 2 < 4 * a(m + 1).
      linarith
  -- b(n) = 2 / (2 * a(n) - 1) implies that a(n) = 1 / b(n) + 1 / 2.
  have hab {n} (hn : 1 ≤ n) : a n = 1 / b n + 1 / 2 := by
    rw [hb n hn]
    field_simp
  -- Prove that b(n) = 2 * n for all n ≥ 1.
  have hb1 {n} (hn : 1 ≤ n) : b n = 2 * n := by
    rw [show n = (n - 1) + 1 by omega]
    -- It is more convenient to prove everything for b(m + 1) for 0 ≤ m.
    generalize n - 1 = m
    induction m with
    -- b(1) = 2 / (2 * a(1) - 1) = 2 / 1 = 2 = 2 * 1.
    | zero => norm_num [hb, ha1]
    | succ m ih =>
      -- Suppose that b(m + 1) = 2 * (m + 1) and show that
      -- b(m + 2) = 2 * (m + 2).
      -- We have b(m + 2) = 2 / (2 * a(m + 2) - 1) = 2 / (2 * (1 - 1 / (4 * a(m + 1))) - 1)
      rw [hb _ (by linarith), han _ (by linarith), show m + 1 + 1 - 1 = m + 1 by omega]
      -- We also have a(m + 1) = 1 / b(m + 1) + 1 / 2 and b(m + 1) = 2 * (m + 1).
      rw [hab (by linarith), ih]
      -- We get b(m + 2) = 2 * (m + 2) with algebraic simplifications.
      field_simp
      ring_nf
  refine ⟨@ha, @hb1, ?_⟩
  -- It is left to show that lim(a(n) / b(n)) = 0 as n tends to infinity.
  -- Show that a(n) / b(n) = (1 / 4) * (1 / n^2 + 1 / n) for all n ≥ 1.
  have eq : (fun n : ℕ => (1 / 4 : ℝ) * (1 / n^2 + 1 / n)) =ᶠ[atTop] (fun n => a n / b n) := by
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    use 1
    intro n hn
    -- The result follows from b(n) = 2 * n and a(n) = 1 / b(n) + 1 / 2 for n ≥ 1.
    rw [hb1 hn, hab hn, hb1 hn]
    ring
  -- Show that lim (1 / 4) * (1 / n^2 + 1 / n) = 0 as n tends to infinity.
  apply Tendsto.congr' eq
  -- We have 0 = (1 / 4) * (0 + 0).
  rw [show (0 : ℝ) = (1 / 4) * (0 + 0) by norm_num]
  apply Tendsto.const_mul
  -- It is left to show that lim (1 / n^2 + 1 / n) = 0 as n tends to infinity.
  apply Tendsto.add
  -- The limit of 1 / n^2 is 0 as n tends to infinity.
  · exact tendsto_const_div_pow 1 2 (by norm_num)
  -- The limit of 1 / n is 0 as n tends to inifinity.
  · exact tendsto_one_div_atTop_nhds_zero_nat