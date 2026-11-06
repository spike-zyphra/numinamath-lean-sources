import Mathlib
-- This problem involves comparing five different decimal representations of a number:
-- Na: A terminating decimal I.d1d2d3d4
-- Nb: A repeating decimal I.d1d2d3d4̅
-- Nc: A mixed decimal I.d1d2d3d4̅ (d2d3d4 repeating)
-- Nd: A mixed decimal I.d1d2d3d4̅ (d3d4 repeating)
-- Ne: A mixed decimal I.d1d2d3d4̅ (d4 repeating)
-- where d3 is strictly greater than d1, d2, d4, and 0
/- Theorem. Let $I$ be an integer and let $d_1, d_2, d_3, d_4$ be four digits, each ranging from 0 to 9.
Consider the following five real numbers:
$N_A = I + \frac{d_1}{10} + \frac{d_2}{100} + \frac{d_3}{1000} + \frac{d_4}{10000}$ (i.e., the terminating decimal $I.d_1d_2d_3d_4$)
$N_B = I + \frac{1000d_640613 + 100d_640613 + 10d_640613 + d_4}{9999}$ (i.e., $I.\overline{d_1d_2d_3d_4}$)
$N_C = I + \frac{d_1}{10} + \frac{100d_640613 + 10d_640613 + d_4}{9990}$ (i.e., $I.d_1\overline{d_2d_3d_4}$)
$N_D = I + \frac{10d_1+d_2}{100} + \frac{10d_3+d_4}{9900}$ (i.e., $I.d_1d_2\overline{d_3d_4}$)
$N_E = I + \frac{100d_1+10d_2+d_3}{1000} + \frac{d_4}{9000}$ (i.e., $I.d_1d_2d_3\overline{d_4}$)

If the digit $d_3$ is strictly greater than $d_1$, $d_2$, $d_4$, and also strictly greater than 0, show that $N_D$ is the largest among $N_A, N_B, N_C, N_D, N_E$. -/
theorem number_theory_640613 (I d1 d2 d3 d4 : ℤ) (Na Nb Nc Nd Ne : ℝ) (h1 : 0 ≤ d1 ∧ d1 ≤ 9) (h2 : 0 ≤ d2 ∧ d2 ≤ 9) (h3 : 0 ≤ d3 ∧ d3 ≤ 9) (h4 : 0 ≤ d4 ∧ d4 ≤ 9) (h5 : d3 > d1 ∧ d3 > d2 ∧ d3 > d4 ∧ d3 > 0) (ha : Na = (I : ℝ) + d1 / 10 + d2 / 100 + d3 / 1000 + d4 / 10000) (hb : Nb = (I : ℝ) + (1000 * d1 + 100 * d2 + 10 * d3 + d4) / 9999) (hc : Nc = (I : ℝ) + d1 / 10 + (100 * d2 + 10 * d3 + d4) / 9990) (hd : Nd = (I : ℝ) + (10 * d1 + d2) / 100 + (10 * d3 + d4) / 9900) (he : Ne = (I : ℝ) + (100 * d1 + 10 * d2 + d3) / 1000 + d4 / 9000) : Nd ≥ Na ∧ Nd ≥ Nb ∧ Nd ≥ Nc ∧ Nd ≥ Ne:= by

  -- Unpack the hypotheses about digit bounds
  rcases h1 with ⟨h1g, -⟩
  rcases h2 with ⟨-, h2l⟩
  rcases h3 with ⟨-, -⟩
  rcases h4 with ⟨h4g, -⟩
  rcases h5 with ⟨h1, h2, h3, h4⟩

  -- Prove that Nd is greater than or equal to all other numbers
  refine ⟨?_, ?_, ?_, ?_⟩
  .
    -- Prove Nd ≥ Na
    suffices Nd - Na ≥ 0 by linarith
    subst Na Nd
    ring_nf
    suffices 10 * d3 + d4 ≥ 0 by rify at this ; linarith
    linarith
  .
    -- Prove Nd ≥ Nb
    suffices Nd - Nb ≥ 0 by linarith
    subst Nd Nb
    ring_nf
    suffices 10 * d3 + d4 - 10 * d1 - d2 ≥ 0 by rify at this ; linarith
    linarith
  .
    -- Prove Nd ≥ Nc
    suffices Nd - Nc ≥ 0 by linarith
    subst Nd Nc
    ring_nf
    suffices d4 + 10 * d3 - 11 * d2 ≥ 0 by rify at this ; linarith
    linarith
  .
    -- Prove Nd ≥ Ne
    suffices Nd - Ne ≥ 0 by linarith
    subst Nd Ne
    ring_nf
    suffices d3 - d4 ≥ 0 by rify at this ; linarith
    linarith
