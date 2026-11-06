import Mathlib

open Finset

/- Example 2 Given a strictly increasing unbounded sequence of positive numbers $a_{1}, a_{2}, \cdots$. Prove:
(1) There exists a natural number $k_{0}$ such that for all $k \geqslant k_{0}$, we have

$$
\frac{a_{1}}{a_{2}}+\frac{a_{2}}{a_{3}}+\cdots+\frac{a_{k}}{a_{k+1}} < k-1 .
$$

(2) When $k$ is sufficiently large, we have $\frac{a_{1}}{a_{2}}+\frac{a_{2}}{a_{3}}+\cdots+\frac{a_{k}}{a_{k+1}} < k-1985$. -/
theorem inequalities_164485 (a : ℕ → ℝ) (ha : StrictMono a)
    (haub : ∀ n, a n > 0) (hb : Set.Unbounded (fun x y => x ≤ y) (a '' Set.univ)) :
    (∃ k0, ∀ k ≥ k0, ∑ i ∈ range k, a i / a (i + 1) < k - 1) ∧
    (∃ k0, ∀ k ≥ k0, ∑ i ∈ range k, a i / a (i + 1) < k - 1985) := by
  -- Prove that for any strictly increasing unbounded sequence of positivie numbers f(i)
  -- there exists k0 such that for all k ≥ k0 the following inequality holds:
  -- ∑ i ∈ range k, f i / f (i + 1) < k - 1 / 2.
  have h {f : ℕ → ℝ} (hf : StrictMono f) (hf_pos : ∀ n, f n > 0) (hfb : Set.Unbounded (fun x y => x ≤ y) (f '' Set.univ)) :
      ∃ k0, ∀ k ≥ k0, ∑ i ∈ range k, f i / f (i + 1) < k - 1 / 2 := by
    -- The sequence f(i) is unbounded so we can find an index j such that 2 * f(0) < f(j).
    replace ⟨b, hfb⟩ := hfb (2 * f 0)
    simp at hfb
    have ⟨j, hj⟩ := hfb.1
    subst b
    -- Take k0 = j + 2.
    use j + 2
    intro k hkj
    -- Show that ∑ i ∈ range k, 1 - ∑ i ∈ range k, f i / f (i + 1) > 1 / 2.
    suffices ∑ i ∈ range k, 1 - ∑ i ∈ range k, f i / f (i + 1) > 1 / 2 by
      simp at this
      linarith
    calc
      -- We have ∑ i ∈ range k, 1 - ∑ i ∈ range k, f i / f (i + 1) = ∑ i ∈ range k, (f (i + 1) - f i) / f (i + 1).
      ∑ i ∈ range k, 1 - ∑ i ∈ range k, f i / f (i + 1) = ∑ i ∈ range k, (f (i + 1) - f i) / f (i + 1) := by
          rw [← sum_sub_distrib]
          apply sum_congr rfl
          intro i hi
          field_simp [ne_of_gt (hf_pos (i + 1))]
      -- f (i + 1) ≤ f k for all i ∈ [0, k) (because f(i) is strictly increasing).
      -- So we get ∑ i ∈ range k, (f (i + 1) - f i) / f (i + 1) ≥ 1 / f k * ∑ i ∈ range k, (f (i + 1) - f i).
      _ ≥ 1 / f k * ∑ i ∈ range k, (f (i + 1) - f i) := by
          rw [mul_sum]
          apply sum_le_sum
          intro i hi
          simp only [mem_range] at hi
          field_simp
          gcongr
          · rw [sub_nonneg]
            exact hf.monotone (by omega)
          · exact hf_pos (i + 1)
          · exact hf.monotone (by omega)
      -- ∑ i ∈ range k, (f (i + 1) - f i) = f(k) - f(0).
      _ = 1 / f k * (f k - f 0) := by rw [sum_range_sub]
      _ = 1 - f 0 / f k := by field_simp [ne_of_gt (hf_pos k)]
      -- f(0) / f(k) < f(0) / (2 * f(0)) = 1 / 2 (because f(k) > f(j) > 2 * f(0)).
      _ > 1 - 1 / 2 := by
          gcongr _ - ?_
          rw [div_lt_div_iff₀ (hf_pos k) zero_lt_two]
          apply lt_trans (mul_comm 2 (f 0) ▸ hfb.2)
          rw [one_mul]
          apply hf
          omega
      _ = 1 / 2 := by norm_num
  -- Generalize the previous result. Prove that for any strictly increasing unbounded sequence of
  -- positive numbers f(i) and for any natural number n there exists k0 such that
  -- for all k ≥ k0, the following inequality holds:
  -- ∑ i ∈ range k, f i / f (i + 1) < k - n * 1 / 2.
  have hn (n : ℕ) {f : ℕ → ℝ} (hf : StrictMono f) (hf_pos : ∀ n, f n > 0) (hfb : Set.Unbounded (fun x y => x ≤ y) (f '' Set.univ)) :
      ∃ k0, ∀ k ≥ k0, ∑ i ∈ range k, f i / f (i + 1) < k - n * 1 / 2 := by
    -- Proof by induction.
    induction n with
    | zero =>
      -- If n = 0 then the result follows from the previous result directly since
      -- x < k - 1 / 2 implies x < k - 0 * 1 / 2.
      simp
      have ⟨k0, hk0⟩ := h hf hf_pos hfb
      use k0
      intro k hk
      linarith [hk0 k hk]
    | succ n ih =>
      -- Suppose that the result holds for n and prove it for n + 1.
      -- We can find k1 such that ∑ i ∈ range k, f i / f (i + 1) < k - n * 1 / 2 for all k ≥ k1.
      have ⟨k1, hk1⟩ := ih
      -- Let g be a sequence defined by g(i) = f(k1 + i).
      set g := fun i => f (k1 + i)
      -- g(i) is positive.
      have hg_pos : ∀ i, g i > 0 := by
        intro i
        simp [g]
        exact hf_pos _
      -- g is strictly increasing.
      have hg : StrictMono g := by
        intro i j hij
        apply hf
        linarith
      -- g is unbounded.
      have hgb : Set.Unbounded (fun x y => x ≤ y) (g '' Set.univ) := by
        intro x
        have ⟨b, hfb⟩ := hfb x
        simp at hfb ⊢
        have ⟨j, hj⟩ := hfb.1
        use j
        simp [g]
        apply lt_of_lt_of_le hfb.2
        rw [← hj]
        apply hf.monotone
        linarith
      -- Use the previous result to find k2 such that
      -- ∑ i ∈ range k, g i / g (i + 1) < k - 1 / 2 for all k ≥ k2.
      have ⟨k2, hk2⟩ := h hg hg_pos hgb
      -- Now take k0 = k1 + k2 and prove that
      -- ∑ i ∈ range k, f i / f (i + 1) < k - (n + 1) * 1 / 2 for all k ≥ k1 + k2.
      use k1 + k2
      intro k hk
      calc
        -- We can rewrite the sum as follows:
        -- ∑ i ∈ range k, f i / f (i + 1) = ∑ i ∈ range k1, f i / f (i + 1) + ∑ i ∈ range (k - k1), g i / g (i + 1).
        ∑ i ∈ range k, f i / f (i + 1) = ∑ i ∈ range k1, f i / f (i + 1) + ∑ i ∈ range (k - k1), g i / g (i + 1) := by
            nth_rw 1 [show k = k1 + (k - k1) by omega, Finset.sum_range_add]
            rfl
        -- The first sum is less than k1 - n * 1 / 2 and the second sum is less than
        -- (k - k1) - 1 / 2 (because k - k1 ≥ k2 when k ≥ k1 + k2).
        _ < (k1 - n * 1 / 2) + (k - k1 - 1 / 2) := by
            gcongr
            · exact hk1 k1 (le_refl _)
            · rw [show (k : ℝ) - k1 = (k - k1 : ℕ) by push_cast [show k ≥ k1 by omega]; rfl]
              exact hk2 _ (by omega)
        -- We obtain that ∑ i ∈ range k, f i / f (i + 1) < k - (n + 1) * 1 / 2.
        _ = k - (n + 1 : ℕ) * 1 / 2 := by
            push_cast
            ring
  -- Now it is easy to prove the theorem statements.
  constructor
  -- To prove that ∑ i ∈ range k, a i / a (i + 1) < k - 1 for all k ≥ k0
  -- use the general result with n = 2 and f = a.
  · have := hn 2 ha haub hb
    norm_num at this
    exact this
  -- To prove that ∑ i ∈ range k, a i / a (i + 1) < k - 1985 for all k ≥ k0
  -- use the general result with n = 2 * 1985 and f = a.
  · have := hn (2 * 1985) ha haub hb
    norm_num at this
    exact this