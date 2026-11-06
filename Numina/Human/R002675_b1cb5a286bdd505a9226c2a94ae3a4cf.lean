import Mathlib

open Topology Filter Real TopologicalSpace Finset
open scoped BigOperators

/- 1. Calculate

(i) $\lim _{n \rightarrow \infty}\left(\frac{1}{\sqrt{n^{2}+1}}+\frac{1}{\sqrt{n^{2}+2}}+\ldots+\frac{1}{\sqrt{n^{2}+n}}\right)$;

(ii) $\lim _{x \rightarrow \infty}\left(1+\frac{1}{[x]}\right)^{x+1}$, where $[x]$ is the integer part of $x \in \mathbb{R}$. -/

-- a eventual lower bound for the series limit
lemma l_series_lb : (∀ᶠ (n : ℕ) in atTop, n / √(n^2 + n) ≤
    (fun n => ∑ i ∈ range n, (1 / √(n ^ 2 + i + 1))) n) := by
  simp
  use 1
  rintro n hn
  -- for n ≥ 1, we can write lower bound as sum of n terms
  convert_to ∑ i ∈ range n, 1 / √(n^2 + n) ≤ _
  . rw [Finset.sum_const]
    simp
    ring
  -- each term is less than corresponding term in series
  apply Finset.sum_le_sum
  rintro i hi
  rw [← one_div, add_assoc]
  gcongr
  norm_cast
  simpa using hi

-- a eventual upper bound for the series limit
lemma l_series_ub : (∀ᶠ (n : ℕ) in atTop, (fun n => ∑ i ∈ range n, (1 / √(n ^ 2 + i + 1))) n
    ≤ n / √(n^2)) := by
  simp
  use 1
  rintro n hn
  -- for n ≥ 1, we can write lower bound as sum of n terms
  convert_to _ ≤ ∑ i ∈ range n, 1 / √(n^2)
  . rw [Finset.sum_const]
    simp
    ring
  -- each term is greater than corresponding term in series
  apply Finset.sum_le_sum
  rintro i hi
  rw [← one_div, add_assoc]
  nth_rw 2 [← add_zero (a := (n^2 : ℝ))]
  gcongr
  norm_cast
  simp

-- limit of lower bound is 1
lemma l_lb_tends_to : Tendsto (fun (n : ℕ) => n / √(n ^ 2 + n)) atTop (𝓝 1) := by
  -- first show that the function is evnetually equal to following which is easier to work with as 1 / n vanishes
  apply Tendsto.congr' (f₁ := (fun (n : ℕ) => 1 / √(1 + 1 / n)))
  . simp [EventuallyEq]
    use 1
    rintro n hn
    field_simp
    rw [← sq_eq_sq₀ (by positivity) (by positivity)]
    ring_nf
    rw [sq_sqrt (by positivity), sq_sqrt (by positivity), sq_sqrt (by positivity)]
    ring
  -- now just apply nomral limit laws
  . nth_rw 4 [show (1 : ℝ) = 1 / √(1 + 0) by simp]
    apply Filter.Tendsto.div
    . simp
    . apply Filter.Tendsto.sqrt
      apply Filter.Tendsto.const_add
      exact tendsto_one_div_atTop_nhds_zero_nat
    . norm_num

-- limit of upper bound is 1
lemma l_ub_tends_to : Tendsto (fun (n : ℕ) => n / √(n ^ 2)) atTop (𝓝 1) := by
  -- show that the function is evnetually equal to 1, hence obvious
  apply Tendsto.congr' (f₁ := (fun (n : ℕ) => 1))
  . simp [EventuallyEq]
    use 1
    rintro n hn
    field_simp
  . simp

-- lower bound of exponential limit
lemma l_exp_lb : (∀ᶠ (x : ℝ) in atTop, (1 + 1 / x) ^ (x + 1) ≤
    (fun (x : ℝ) => (1 + 1 / (⌊x⌋ : ℝ)) ^ (x + 1)) x) := by
  -- for 1 ≤ x, the bound is true as x ≥ ⌊x⌋
  simp
  use 1
  rintro x hx
  gcongr
  . norm_cast
    apply Int.le_floor.mpr
    simpa
  . exact Int.floor_le x

-- upper bound of exponential limit
lemma l_exp_ub : (∀ᶠ (x : ℝ) in atTop, (fun (x : ℝ) => (1 + 1 / (⌊x⌋ : ℝ)) ^ (x + 1)) x ≤
    (1 + 1 / (x - 1)) ^ (x + 1)) := by
  -- for 2 ≤ x, the bound is true as x ≤ ⌊x⌋ + 1
  simp
  use 2
  rintro x hx
  gcongr
  . linarith
  . linarith [Int.lt_floor_add_one x]

-- limit of lower bound is exp(1)
lemma l_lb_tends_to' : Tendsto (fun (x : ℝ) => (1 + 1 / x) ^ (x + 1)) atTop (𝓝 (rexp 1)) := by
  -- write the function as exponential limit * (1 + 1 / x), this is true for x ≥ 0
  apply Tendsto.congr' (f₁ := (fun (x : ℝ) => (1 + 1 / x) ^ x * (1 + 1 / x)))
  . simp [EventuallyEq]
    use 0
    rintro x hx
    rw [Real.rpow_add_one (by positivity)]
  -- now just use limit laws
  . rw [show exp 1 = (exp 1) * (1 + 0) by ring]
    apply Filter.Tendsto.mul
    . apply tendsto_one_plus_div_rpow_exp
    . apply Filter.Tendsto.const_add
      simp
      apply tendsto_inv_atTop_zero

-- limit of upper bound is exp(1)
lemma l_ub_tends_to' : Tendsto (fun (x : ℝ) => (1 + 1 / (x - 1)) ^ (x + 1)) atTop (𝓝 (rexp 1)) := by
  -- first write the function as composition of a function on (x => x - 1)
  have h_comp : (fun (x : ℝ) ↦ (1 + 1 / (x - 1)) ^ (x + 1)) = (fun (x : ℝ) ↦ (1 + 1 / x)^(x + 2)) ∘
      (fun (x : ℝ) ↦ x - 1) := by
    ext x
    simp
    congr 1
    ring
  rw [h_comp]
  -- now use composition law, x - 1 tends to ∞ as x tends to ∞
  apply Filter.Tendsto.comp (y := atTop)
  -- with simpler version with out x - 1, write the function as exponential limit * (1 + 1 / x)^2, true for x ≥ 0
  . apply Tendsto.congr' (f₁ := (fun (x : ℝ) => (1 + 1 / x) ^ x * (1 + 1 / x) ^ 2))
    . simp [EventuallyEq]
      use 0
      rintro x hx
      rw [Real.rpow_add (by positivity)]
      simp
    -- now just apply limit laws
    . rw [show exp 1 = (exp 1) * (1 + 0)^2 by ring]
      apply Filter.Tendsto.mul
      . apply tendsto_one_plus_div_rpow_exp
      . apply Filter.Tendsto.pow
        apply Filter.Tendsto.const_add
        simp
        apply tendsto_inv_atTop_zero
  . apply tendsto_atTop_add_const_right atTop (-1)
    apply Filter.tendsto_id

theorem calculus_98680_1 :
  Tendsto (λ n => ∑ i ∈ range n, (1 / √(n ^ 2 + i + 1))) atTop (𝓝 1) := by
  -- just use squeeze theorem with lemmas
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' l_lb_tends_to l_ub_tends_to l_series_lb l_series_ub

theorem calculus_98680_2 :
  Tendsto (λ (x : ℝ) => (1 + 1 / (⌊x⌋ : ℝ)) ^ (x + 1)) atTop (𝓝 (exp 1)) := by
  -- just use squeeze theorem with lemmas
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' l_lb_tends_to' l_ub_tends_to' l_exp_lb l_exp_ub