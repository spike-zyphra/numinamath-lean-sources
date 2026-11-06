import Mathlib

open Finset Real

/-For a positive integer $n,$ let
\[a_n = \sum_{k = 0}^n \frac{1}{\binom{n}{k}} \quad \text{and} \quad b_n = \sum_{k = 0}^n \frac{k}{\binom{n}{k}}.\]Simplify $\frac{a_n}{b_n}.$-/
theorem algebra_15669 {n : ℕ} (hn: 0 < n):
    (∑ k in range (n + 1), (1 : ℝ) / Nat.choose n k) /
    (∑ k in range (n + 1), (k : ℝ) / Nat.choose n k) = 2 / n := by
  -- For the sum $b_n,$ let $j = n - k,$ so $k = n - j.$  Then
  -- \begin{align*}
  -- b_n &= \sum_{k = 0}^n \frac{k}{\binom{n}{k}} \\
  -- &= \sum_{j = n}^0 \frac{n - j}{\binom{n}{n - j}} \\
  -- &= \sum_{j = 0}^n \frac{n - j}{\binom{n}{j}} \\
  -- &= \sum_{k = 0}^n \frac{n - k}{\binom{n}{k}},
  -- \end{align*}
  obtain ⟨a, ha⟩ := (by simp: ∃a, a = ∑ k in range (n + 1), (1 : ℝ) / Nat.choose n k)
  obtain ⟨b, hb⟩ := (by simp: ∃b, b = ∑ k in range (n + 1), (k : ℝ) / Nat.choose n k)
  rw [ha.symm, hb.symm]
  have b_eq : ∑ k in range (n + 1), (k : ℝ) / Nat.choose n k = ∑ j in range (n + 1), (n - j : ℝ) / Nat.choose n j := by
    obtain ⟨f, hf⟩ := (by simp: ∃(f : ℕ → ℕ), f = fun x => n - x)
    rw [Finset.sum_of_injOn]
    use f
    rw [hf]
    apply StrictAntiOn.injOn
    intro a ha b hb hab
    simp at ha hb
    simp
    omega
    apply Set.mapsTo'.mpr
    apply Set.toFinset_subset.mp
    have : (f '' ↑(range (n + 1))).toFinset = range (n + 1) := by
      ext i
      simp
      constructor
      . intro ha
        rcases ha with ⟨a, ha⟩
        rw [hf] at ha
        simp at ha
        omega
      . intro ha
        rw [hf]
        simp
        use n - i
        omega
    rw [this]
    rw [hf]
    simp
    intro i hi hx
    specialize hx (n - i)
    omega
    rw [hf]
    simp
    intro i hi
    have : ((n : ℝ) - (n - i : ℕ)) = i := by
      rw [Nat.cast_sub]
      linarith
      linarith
    rw [Nat.choose_symm, this]
    linarith
  -- so, b_n + b_n = \sum_{k = 0}^n \frac{k}{\binom{n}{k}} + \sum_{k = 0}^n \frac{n - k}{\binom{n}{k}} = \sum_{k = 0}^n \frac{n}{\binom{n}{k}} = n \sum_{k = 0}^n \frac{1}{\binom{n}{k}} = na_n.
  have two_b: 2 * b = n * a := by
    rw [hb, two_mul]
    rw (config := { occs := .pos [2]}) [b_eq]
    have : ∑ j in range (n + 1), (n - j : ℝ) / Nat.choose n j = ∑ k in range (n + 1), (n: ℝ) / Nat.choose n k - ∑ k in range (n + 1), (k : ℝ) / Nat.choose n k := by
      have : (fun (x : ℕ) ↦ (n : ℝ) / (n.choose x) - (x : ℝ) / (n.choose x)) = (fun (j : ℕ) ↦ (n - j : ℝ) / (n.choose j)) := by
        funext x
        ring_nf
      rw [←Finset.sum_sub_distrib, Finset.sum, Finset.sum, this, ←Finset.sum]
    rw [this, add_sub]
    simp
    have : (fun (i : ℕ) ↦ (n : ℝ) * (1 / (n.choose i))) = (fun (i : ℕ) ↦ (n : ℝ) / (n.choose i)) := by
      funext i
      rw [mul_div, mul_one]
    rw [ha, Finset.mul_sum, Finset.sum, Finset.sum, this, ←Finset.sum]
  -- Then $2b_n = na_n,$ so $\frac{a_n}{b_n} = \boxed{\frac{2}{n}}.$
  apply (div_eq_div_iff ?_ ?_).mpr
  rw [two_b, mul_comm]

  -- prove that b_n ≠ 0, if b_n = 0, than, a = 0 ∨ n = 0 by two_b: 2 * b = n * a
  intro hb
  rw [hb] at two_b
  simp at two_b
  obtain (r | r) := two_b
  . -- n = 0
    linarith [Nat.not_eq_zero_of_lt hn]
  . -- a = 0
    rw [Finset.sum_range_succ] at ha
    simp at ha
    have : 0 ≤ ∑ x ∈ range n, ((n.choose x) : ℝ)⁻¹ := by
      apply Finset.sum_nonneg
      simp
    linarith
  norm_cast
  exact (Nat.not_eq_zero_of_lt hn)
