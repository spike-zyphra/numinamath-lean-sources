import Mathlib

open Polynomial

/- Find all polynomials $P(x)$ with real coefficients such that

$$
(x-2010) P(x+67)=x P(x)
$$

for every integer $x$. -/
theorem algebra_606439 :
    {P : ℝ[X] | ∀ x : ℤ, (x - 2010) * P.eval (x + 67 : ℝ) = x * P.eval (x : ℝ)} = {C c * ∏ i ∈ Finset.range 30, (X - C ((i + 1 : ℝ) * 67)) | c : ℝ} := by
  -- Two trivial but useful equalities
  -- They are used in both directions of the proof
  have k₁ (x : ℝ) : (x - 2010) * ((∏ i ∈ Finset.range 30, (x + 67 - (i + 1) * 67))) = ∏ i ∈ Finset.range 31, (x - i * 67) := by
    nth_rw 2 [Finset.prod_range_succ, mul_comm]
    congr
    . norm_num
    . ext i
      ring
  have k₂ (x : ℝ) : x * ((∏ i ∈ Finset.range 30, (x - (i + 1) * 67))) = ∏ i ∈ Finset.range 31, (x - i * 67) := by
    nth_rw 2 [Finset.prod_range_succ', mul_comm]
    congr
    . simp
    . ext i
      simp
  -- The proof is done in two directions
  ext P
  constructor
  . -- WLOG, assume $P$ is non-zero
    wlog hPne0 : P ≠ 0
    {
      -- If P = 0, then we set c = 0
      simp at hPne0
      intro H
      use 0
      simp [hPne0]
    }
    intro H
    simp at H
    -- 67, 2 * 67, ..., 30 * 67 are roots of P
    have h₁ (i : ℕ) : i < 30 → P.eval ((i + 1 : ℝ) * 67) = 0 := by
      -- Induction on i
      induction i with
      | zero => simpa using H 0 -- Base case, take x = 0 in the given equality
      | succ i ih =>
        -- Inductive step, take x = (i + 1) * 67 in the given equality
        intro hi
        specialize H ((i + 1) * 67)
        specialize ih (Nat.lt_of_succ_lt hi)
        simp [ih] at H
        rw [or_iff_right (by rify at hi; linarith)] at H
        convert H using 2
        rify
        ring
    -- 67, 2 * 67, ..., 30 * 67 are roots of P
    have h₂ : ((Finset.range 30).val).map (fun (i : ℕ) => (i + 1 : ℝ) * 67) <= P.roots := by
      -- There are no duplicate elements in the list
      rw [Multiset.le_iff_subset (Multiset.Nodup.map (by intro i j hij; simpa using hij) (Finset.range 30).nodup)]
      -- Logically trivial
      intro x hx
      simp [-Multiset.range_succ] at hx
      rcases hx with ⟨i, hi, hix⟩
      simp [hPne0, ← hix, h₁ i hi]
    -- So (X - 67)(X - 2 * 67)...(X - 30 * 67) divides P
    rw [← Multiset.prod_X_sub_C_dvd_iff_le_roots hPne0, Multiset.map_map] at h₂
    have h₃ : (Multiset.map ((fun a => X - C a) ∘ fun (i : ℕ) => (i + 1 : ℝ) * 67) (Finset.range 30).val).prod = ∏ i ∈ Finset.range 30, (X - C ((i + 1 : ℝ) * 67) : ℝ[X]) := by
      rw [Finset.prod]
      congr
    -- So P = Q * (X - 67)(X - 2 * 67)...(X - 30 * 67) for some Q
    obtain ⟨Q, rfl⟩ := h₃ ▸ h₂
    clear h₁ h₂ h₃
    -- It suffices to show that Q is a constant polynomial
    suffices ∃ c : ℝ, Q = C c by
      obtain ⟨c, rfl⟩ := this
      rw [mul_comm]
      simp
    -- Simplify the given equality
    simp [eval_mul, eval_prod, ← mul_assoc] at H
    simp [k₁, k₂, Finset.prod_eq_zero_iff] at H
    clear k₁ k₂
    -- We have Q(x + 67) = Q(x) as a polynomial identity
    have h₁ : Q.comp (X + 67) = Q := by
      -- It suffices to show that the two polynomials are equal on an infinite set
      apply Polynomial.eq_of_infinite_eval_eq
      -- Specifically, the set of integers greater than 2010
      apply Set.Infinite.mono (s := (Set.Ioi 2010).image Int.cast)
      . -- The second part of `H` does not hold for x > 2010, so we have Q(x + 67) = Q(x)
        intro x hx
        simp at hx ⊢
        rcases hx with ⟨x, hx, rfl⟩
        specialize H x
        rwa [or_iff_left] at H
        simp
        intro i h₁ h₂
        rw [sub_eq_zero] at h₂
        norm_cast at h₂
        omega
      . -- The set of integers greater than 2010 is infinite
        exact Set.Infinite.image (Function.Injective.injOn Int.cast_injective) (Set.Ioi_infinite _)
    -- Now we show that Q is a constant polynomial
    have h₂ : Q = C (Q.eval 0) := by
      -- It suffices to show that the two polynomials are equal on an infinite set
      apply Polynomial.eq_of_infinite_eval_eq
      -- Specifically, the set {n * 67 | n ∈ ℕ}
      apply Set.Infinite.mono (s := Set.range (fun (n : ℕ) => (n : ℝ) * 67))
      . -- Q(0) = Q(67) = Q(2 * 67) = ...
        intro x hx
        simp at hx ⊢
        rcases hx with ⟨i, rfl⟩
        -- An easy induction can prove this
        induction i with
        | zero => simp
        | succ i ih =>
          apply_fun (·.eval (i * 67 : ℝ)) at h₁
          simp at h₁
          rw [Nat.cast_succ, add_mul, one_mul, h₁, ih]
      . -- The set {n * 67 | n ∈ ℕ} is infinite
        exact Set.infinite_range_of_injective (by intro i j hij; simpa using hij)
    exact ⟨Q.eval 0, h₂⟩
  . -- Conversely, we show that the polynomials of that form satisfy the given property
    rintro ⟨c, rfl⟩ x
    simp [eval_mul, eval_prod]
    -- Change the order of the products
    rw [← mul_assoc, mul_comm _ c, mul_assoc, k₁]
    rw [← mul_assoc, mul_comm _ c, mul_assoc, k₂]
