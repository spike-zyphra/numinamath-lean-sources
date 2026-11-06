import Mathlib

open Real

/- Soit $a \in] 0 ; 1\left[\right.$ et $n>0$ un entier. On note $f_{n}$ la fonction définie sur $\mathbb{R}$ par $f_{n}(x)=x+\frac{x^{2}}{n}$, pour tout réel $x$. Prouver que

$$
\frac{a(1-a) n^{2}+2 a^{2} n+a^{3}}{(1-a)^{2} n^{2}+a(2-a) n+a^{2}}<\underbrace{\left(f_{n} \circ f_{n} \circ \cdots \circ f_{n}\right)}_{n}(a)<\frac{a n+a^{2}}{(1-a) n+a} .
$$ -/
theorem inequalities_607581 (a : ℝ) (ha : 0 < a ∧ a < 1) (n : ℕ) (hn : 0 < n)
    (f : ℕ → ℕ → ℝ → ℝ) (hfn : ∀ x n, f n 1 x = x + x ^ 2 / n) (hfnk : ∀ n, ∀ k > 0, f n (k + 1) = f n 1 ∘ f n k) :
    (a * (1 - a) * n ^ 2 + 2 * a ^ 2 * n + a ^ 3) / ((1 - a) ^ 2 * n ^ 2 + a * (2 - a) * n + a ^ 2) <
    (f n n a) ∧ (f n n a) ≤ (a * n + a ^ 2) / ((1 - a) * n + a) := by

  -- suppose t n = f n a
  set t : ℕ → ℝ := λ k => if k > 0 then f n k a else a with ht

  -- substitute t n into expressions
  -- simplify the conclusion
  have eq : t n = f n n a := by rw [ht]; simp [hn]
  rw [<-eq]
  clear eq
  -- simplify the recursive formula
  replace hfnk : ∀ k > 0, t (k + 1) = t k + t k ^ 2 / n := by
    intro k hk
    rw [ht] -- use the difinition of t
    simp [hk]
    rw [hfnk n k hk] -- substitute recursive formula
    simp
    rw [hfn] -- use the difinition of f n 1
  -- expand the recursive formula
  replace hfnk :∀ k, t (k + 1) = t k + t k ^ 2 / n := by
    intro k
    cases k with
      | zero => -- when k = 0
        simp
        exact hfn a n
      | succ k => -- when k > 0
        have h := hfnk (k + 1)
        norm_num at h
        exact h

  -- show that 0 < t k
  have ht_pos : ∀ k, 0 < t k ∧ t k < t (k + 1):= by
    intro k
    induction k with
    | zero => -- when k = 0
      simp
      refine ⟨?_, ?_⟩
      -- show that 0 < a
      . rw [ht]
        simp
        exact ha.1
      -- show that a < a + a ^ 2 / n
      . have h := hfnk 0
        norm_num at h
        rw [h, ht]
        simp
        apply div_pos
        nlinarith only [ha.1]
        norm_cast
    | succ k ih => -- when k > 0
      have h : 0 < t (k + 1) := by linarith only [ih.1, ih.2]
      refine ⟨?_, ?_⟩
      -- show that 0 < t (k + 1)
      . exact h
      -- show that t (k + 1) < t (k + 1 + 1)
      . rw [hfnk (k + 1)]
        simp
        apply div_pos
        nlinarith only [h]
        norm_cast

  -- show that t 0 ≤ t k
  have hinf : ∀ k, t 0 ≤ t k := by
    intro k
    induction k with
    | zero => -- when k = 0
      simp
    | succ k ih => -- when k > 0
      have h := hfnk k
      norm_num at h
      linarith only [ih, ht_pos k]

  -- show that t k < t n
  have hsup : ∀ k < n, t k < t n := by
    intro k hk
    -- first show that t k - t n > 0
    have h : t n - t k > 0 := by
      calc
        t n - t k = ∑ i in Finset.range n, (t (i + 1) - t i) - ∑ i in Finset.range k, (t (i + 1) - t i) := by repeat rw [Finset.sum_range_sub]; ring_nf
        _ = ∑ i in Finset.range (k + (n - k)), (t (i + 1) - t i) - ∑ i in Finset.range k, (t (i + 1) - t i) := by rw [Nat.add_sub_of_le]; linarith only [hk]
        -- calculate the sub of two sums
        _ = ∑ i in Finset.range (n - k), (t (i + k + 1) - t (i + k)) := by
          rw [Finset.sum_range_add_sub_sum_range]
          rw [Finset.sum_congr]
          simp
          simp
          ring_nf
          tauto
        -- simplify the terms
        _ = ∑ i in Finset.range (n - k), t (i + k) ^ 2 / n := by
          rw [Finset.sum_congr]
          simp
          intro x hx
          linarith only [hfnk (x + k)]
        _ > 0 := by
          apply Finset.sum_pos
          intro i hi
          -- show that t (i + k) ^ 2 / n > 0
          apply div_pos
          nlinarith only [ht_pos (i + k)]
          norm_cast
          -- show that (Fins.range (n - k)).nonempty
          simp
          contrapose! hk
          apply Nat.le_of_sub_eq_zero hk

    linarith only [h]

  -- simplify the expression further
  replace hfnk : ∀ k, 1 / t (k + 1) = 1 / t k - 1 / (t k + n) := by
    intro k
    -- show that denominators is not zero
    have hk1 : t (k + 1) ≠ 0 := by linarith only [ht_pos (k + 1)]
    have hk : t k ≠ 0 := by linarith only [ht_pos k]
    have hkn : t k + n ≠ 0 := by linarith only [ht_pos k]
    -- simplify the expression
    field_simp [ht_pos k]
    rw [hfnk]
    field_simp
    ring_nf
  -- simplify the expression to variation terms
  replace hfnk : ∀ k, 1 / (t k + n) = 1 / t k - 1 / t (k + 1) := by
    intro k
    linarith only [hfnk k]

  -- so we have 1 / t n = 1 / a - ∑ i : Fin n, 1 / (a i + n)
  replace hfn : 1 / t n = 1 / a - ∑ i : Finset.range n, 1 / (t i + n) := by
    replace hfn : ∑ i : Finset.range n, 1 / (t i + n) = 1 / a - 1 / t n := by
      calc
        ∑ i : Finset.range n, 1 / (t i + n) = ∑ i : Finset.range n, (1 / t i - 1 / t (i + 1)) := by
          apply Finset.sum_congr
          simp
          intro i hi
          exact hfnk i
        -- change Finset.range n to (Finset.range n).attach
        _ = ∑ i ∈ Finset.range n, (1 / t i - 1 / t (i + 1)) := by
          nth_rewrite 2 [<-Finset.sum_attach]
          simp
        _ = 1 / a - 1 / t n := by rw [Finset.sum_range_sub' (λ i => 1 / t i) n]; rw [ht]; simp
    -- easily linear calculation
    linarith only [hfn]

  -- show the right part of the conclusion
  have conc1 : t n ≤ (a * n + a ^ 2) / ((1 - a) * n + a) := by
    -- show that ∑ 1 / (t i + n) < ∑ 1 / (t 0 + n)
    have ineq : ∑ i : Finset.range n, 1 / (t i + n) ≤ ∑ i : Finset.range n, 1 / (t 0 + n) := by
      apply Finset.sum_le_sum
      simp
      intro a ha
      -- show that 1 / (t a + n) ≤ 1 / (t 0 + n)
      rw [inv_le_inv₀]
      linarith only [hinf a]
      linarith only [ht_pos a]
      linarith only [ht_pos 0]

    -- show that ∑ 1 / (t 0 + n) = n / (t 0 + n)
    have eq : ∑ i : Finset.range n, 1 / (t 0 + n) = n / (t 0 + n) := by
      rw [Finset.sum_const]
      simp
      ring_nf
    rw [eq] at ineq
    clear eq

    -- prepare for the final calculation
    replace ineq : 1 / a - ∑ i : Finset.range n, 1 / (t i + n) ≥ 1 / a - n / (t 0 + n) := by
      apply sub_le_sub_left
      simp at ineq ⊢
      exact ineq

    -- calculate the result of 1 / t n
    replace ineq : ((a * n + a ^ 2) / ((1 - a) * n + a))⁻¹ ≤ (t n)⁻¹ := by
      calc
        ((a * n + a ^ 2) / ((1 - a) * n + a))⁻¹ = ((1 - a) * n + a) / (a * n + a ^ 2) := by rw [inv_div]
        _ = 1 / a - n / (t 0 + n) := by
          -- get 0 < 1 - a
          obtain ⟨ha1, ha2⟩ := ha
          replace ha2 : 0 < 1 - a := by linarith only [ha2]
          rw [ht]
          simp
          field_simp
          ring_nf
        _ ≤ 1 / a - ∑ i : Finset.range n, 1 / (t i + n) := by exact ineq
        _ = 1 / (t n) := by rw [hfn]
        _ = (t n)⁻¹ := by ring_nf

    obtain ⟨ha1, ha2⟩ := ha
    replace ha2 : 0 < 1 - a := by linarith only [ha2]
    -- cancel the inv
    rw [inv_le_inv₀] at ineq
    exact ineq
    -- prove the positivity of the fraction
    apply div_pos
    positivity
    positivity
    linarith only [ht_pos n]

  -- show the left part of the conclusion
  have conc2 : (a * (1 - a) * n ^ 2 + 2 * a ^ 2 * n + a ^ 3) / ((1 - a) ^ 2 * n ^ 2 + a * (2 - a) * n + a ^ 2) < t n := by
    -- show that ∑ 1 / (t i + n) > ∑ 1 / (t n + n)
    have ineq : ∑ i : Finset.range n, 1 / (t i + n) > ∑ i : Finset.range n, 1 / (t n + n) := by
      apply Finset.sum_lt_sum
      simp
      intro a ha
      -- show that 1 / (t a + n) > 1 / (t n + n)
      rw [inv_le_inv₀]
      apply add_le_add_right
      linarith only [hsup a ha]
      linarith only [ht_pos n]
      linarith only [ht_pos a]
      . -- show that 1 / (t n + n) < 1 / (t (n - 1) + n)
        simp
        use (n - 1)
        norm_num
        refine ⟨?_, ?_⟩
        -- show that 0 < n
        . exact hn
        -- show that 1 / (t n + n) < 1 / (t (n - 1) + n)
        . rw [inv_lt_inv₀]
          have h1 := ht_pos (n - 1)
          rw [Nat.sub_one_add_one] at h1
          linarith only [h1.2]
          positivity
          linarith only [ht_pos n]
          linarith only [ht_pos (n - 1)]

    -- show that ∑ 1 / (t n + n) = n / (t n + n)
    have eq : ∑ i : Finset.range n, 1 / (t n + n) = n / (t n + n) := by
      rw [Finset.sum_const]
      simp
      ring_nf
    rw [eq] at ineq
    clear eq

    -- substitute t n < (a * n + a ^ 2) / ((1 - a) * n + a)
    have ineq2 : 1 / a - n / (t n + n) ≤ 1 / a - n / (((a * n + a ^ 2) / ((1 - a) * n + a)) + n) := by
      apply sub_le_sub_left
      apply div_le_div_of_nonneg_left
      positivity
      linarith only [ht_pos n]
      linarith only [conc1]

    -- prepare for the final calculation
    replace ineq : 1 / a - ∑ i : Finset.range n, 1 / (t i + n) < 1 / a - n / (t n + n) := by
      field_simp
      simp at ineq ⊢
      exact ineq

    -- calculate the result of 1 / t n
    replace ineq : (t n)⁻¹ < ((a * (1 - a) * n ^ 2 + 2 * a ^ 2 * n + a ^ 3) / ((1 - a) ^ 2 * n ^ 2 + a * (2 - a) * n + a ^ 2))⁻¹ := by
      calc
        (t n)⁻¹ = 1 / t n := by ring_nf
        _ = 1 / a - ∑ i : Finset.range n, 1 / (t i + n) := by rw [hfn]
        _ < 1 / a - n / (t n + n) := by exact ineq
        _ ≤ 1 / a - n / (((a * n + a ^ 2) / ((1 - a) * n + a)) + n) := by exact ineq2
        _ = ((1 - a) ^ 2 * n ^ 2 + a * (2 - a) * n + a ^ 2) / (a * (1 - a) * n ^ 2 + 2 * a ^ 2 * n + a ^ 3) := by
          -- get 0 < 1 - a
          obtain ⟨ha1, ha2⟩ := ha
          replace ha2 : 0 < 1 - a := by linarith only [ha2]
          field_simp
          ring_nf
        _ = ((a * (1 - a) * n ^ 2 + 2 * a ^ 2 * n + a ^ 3) / ((1 - a) ^ 2 * n ^ 2 + a * (2 - a) * n + a ^ 2))⁻¹ := by
          rw [inv_div]

    obtain ⟨ha1, ha2⟩ := ha
    replace ha2 : 0 < 1 - a := by linarith only [ha2]
    -- cancel the inv
    rw [inv_lt_inv₀] at ineq
    exact ineq
    -- prove the positivity of the fraction
    linarith only [ht_pos n]
    apply div_pos
    positivity
    have ha3 : 0 < 2 - a := by linarith only [ha2]
    positivity

  tauto