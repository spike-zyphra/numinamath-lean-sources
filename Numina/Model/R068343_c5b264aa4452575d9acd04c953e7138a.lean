import Mathlib

open Finset

theorem number_theory_104831 {a b c : ℕ}
    (ha : a = sInf {x | ∃ m ∈ Icc 1 (10 ^ 2), x = m ∧ n ∣ m ∧ ¬∃ k < n, m ∈ Icc 1 (k ^ 2)})
    (hb : ∀ n ≥ 3, (n ^ 2 - n) ∈ Icc 1 (n ^ 2) ∧ (n ^ 2 - 2 * n) ∈ Icc 1 (n ^ 2))
    (hc : IsGreatest {n | 0 < n ∧ ¬(n ^ 2 - 10 * n) ∈ Icc 1 (n ^ 2)} 30) :
    a = 10 ∧ b = 30 ∧ c = 10 := by
  -- To show 30 is in the set {n | 0 <n ∧ ¬ (n^2 -10n) ∈ [1,n^2]}, we prove contradiction
  have h1 : ¬ (30 : ℕ) ∈ {n | 0 < n ∧ ¬(n ^ 2 - 10 * n) ∈ Icc 1 (n ^ 2)} := by
    simp only [Set.mem_setOf_eq]
    -- Compute, 30>0, and 30^2-10×30=900-300=600
    -- 600 ∈ [1,900], so ¬(600 ∈ [1,900]) is false
    norm_num [Finset.mem_Icc]
  -- From the definition of IsGreatest, 30 must be in the set
  have h2 : (30 : ℕ) ∈ {n | 0 < n ∧ ¬(n ^ 2 - 10 * n) ∈ Icc 1 (n ^ 2)} := by
    exact hc.left
  contradiction