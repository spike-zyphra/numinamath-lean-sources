import Mathlib

open Nat

/--
Let `p` be a prime and `k` be a nonnegative integer.  Then the exponent of `p` in
`(p^k)!` is exactly `(p^k - 1) / (p - 1)`.  In other words,
factorization (factorial (p ^ k)) p = (p ^ k - 1) / (p - 1).
This is the usual "Legendre's formula" specialized to `n = p^k`.
-/
theorem exponent_of_prime_in_primePow_factorial {p : ℕ} [Fact (Nat.Prime p)] (k : ℕ) : (factorial (p ^ k)).factorization p = (p ^ k - 1) / (p - 1) := by
  -- We begin by invoking the version of Legendre's formula in Mathlib:
  -- `factorization_factorial` says
  --   `factorization (n!) p = ∑ i ∈ Finset.range (n + 1), n / p^i`
  -- for any prime `p` and `n : ℕ`.  We now specialize to `n = p ^ k`.

  have hp : Nat.Prime p := Fact.out
  have hp_gt_1 : 1 < p := hp.one_lt

  have h_log : log p (p ^ k) < k + 1 := by
    -- `log p (p^k) = k` because p > 1, and k < k + 1
    have : log p (p ^ k) = k := log_pow hp_gt_1 k
    rw [this]
    exact Nat.lt_succ_self k

  -- 2. Apply Legendre’s theorem (Nat.Prime.emultiplicity_factorial).
  have h_legendre :
    emultiplicity p ((p ^ k).factorial) =
      ↑(∑ i ∈ Finset.Ico 1 (k + 1), (p ^ k) / p ^ i) := by
    apply Nat.Prime.emultiplicity_factorial hp h_log

  -- Rewrite our goal using that identity.
  -- Rewrite `factorization` in terms of `emultiplicity` (and `toNat`)
  have h_factor_to_emult :
    (factorial (p ^ k)).factorization p = (emultiplicity p ((p ^ k).factorial)).toNat := by
    have mul_eq_factorization : multiplicity p (p ^ k)! = (p ^ k)!.factorization p := Nat.multiplicity_eq_factorization hp (factorial_ne_zero (p ^ k))

    have : (emultiplicity p ((p ^ k).factorial)).toNat = multiplicity p ((p ^ k).factorial) := by
      have h_finite : FiniteMultiplicity p (factorial (p ^ k)) := by
        exact finiteMultiplicity_of_emultiplicity_eq_natCast h_legendre
      have :emultiplicity p (p ^ k)! = ↑(multiplicity p (p ^ k)!) := FiniteMultiplicity.emultiplicity_eq_multiplicity h_finite
      simp [this]

    simp_all

  -- Replace `factorial (p^k)).factorization p` by `(emultiplicity p ((p^k)!)).toNat`,
  -- then substitute the Legendre sum, producing a goal of the form
  --   `(↑(∑ i ∈ Ico 1 (k + 1), p^k / p^i)).toNat = (p^k - 1) / (p - 1)`.
  rw [h_factor_to_emult, h_legendre]

  have geom_sum:
    ∑ i ∈ Finset.Ico 1 (k + 1), (p ^ k) / (p ^ i) = (p ^ k - 1) / (p - 1) := by
    -- We will rewrite `(p^k) / (p^i)` as `p^(k - i)` whenever `1 ≤ i < k+1`.
    have hp : Nat.Prime p := Fact.out
    have h_pos : 1 < p := hp.one_lt

    -- 1) Show that for each `i ∈ Ico 1 (k + 1)`, we have `i ≤ k`.
    have le_i_k : ∀ i, i ∈ Finset.Ico 1 (k + 1) → i ≤ k := by
      intro i hi
      -- `mem_Ico.mp hi` gives `1 ≤ i` and `i < k + 1`. From `i < k + 1` we get `i ≤ k`.
      exact Nat.le_of_lt_succ (Finset.mem_Ico.mp hi).2

    -- 2) For any `i` with `1 ≤ i < k+1`, rewrite `(p^k) / (p^i) = p^(k - i)`.
    have term_eq : ∀ i, i ∈ Finset.Ico 1 (k + 1) → (p ^ k) / (p ^ i) = p ^ (k - i) := by
      intro i hi
      let hi₁ : i ≤ k := le_i_k i hi
      -- Because `i ≤ k`, we know `(k - i) + i = k`.
      have add_tsub : i + (k - i) = k := by omega
      -- Now `p^k = p^(i + (k - i)) = p^i * p^(k - i)` by `Nat.pow_add`.
      have pow_mul : p ^ k = p ^ i * p ^ (k - i) := by
        calc
          p ^ k = p ^ (i + (k - i)) := by exact congrArg (HPow.hPow p) (id (Eq.symm add_tsub))
          _     = p ^ i * p ^ (k - i) := by ring
      -- From `p^k = p^i * p^(k - i)` and `p^i ≠ 0`, we get `(p^k) / (p^i) = p^(k - i)`.
      rw [pow_mul, Nat.mul_div_cancel_left _ (pow_pos (Nat.Prime.pos hp) i)]

    -- 3) Replace every term `(p^k)/(p^i)` by `p^(k - i)` inside the sum.
    have sum₁ : ∑ i ∈ Finset.Ico 1 (k + 1), (p ^ k) / (p ^ i) = ∑ i ∈ Finset.Ico 1 (k + 1), p ^ (k - i) := Finset.sum_congr rfl term_eq

    -- 4) Now we want to convert `∑ i ∈ Ico 1 (k + 1), p^(k - i)` into `∑ j ∈ range k, p^j`.
    --    The map `i ↦ k - i` is a bijection between `Ico 1 (k+1)` and `range k = {0,1,…,k-1}`.

    --    We'll use `Finset.sum_bij`:

    have sum₂ :
      ∑ i ∈ Finset.Ico 1 (k + 1), p ^ (k - i) = ∑ j ∈ Finset.range k, p ^ j := by
      apply Finset.sum_bij (fun i _hi => k - i)
      · -- Proof that (k - i) ∈ range k for i ∈ Ico 1 (k + 1)
        intro i hi
        have hi₁ : 1 ≤ i := (Finset.mem_Ico.mp hi).1
        have hi₂ : i < k + 1 := (Finset.mem_Ico.mp hi).2
        have le_i_k := Nat.le_of_lt_succ hi₂  -- `i ≤ k`
        have hklt : k - i < k := by omega
        exact Finset.mem_range.2 hklt
      · -- Injectivity
        intro i₁ hi₁ i₂ hi₂ h_eq
        have le₁ : i₁ ≤ k := le_i_k i₁ hi₁
        have le₂ : i₂ ≤ k := le_i_k i₂ hi₂
        omega
      · -- Surjectivity
        intro j hj
        have hj_lt : j < k := Finset.mem_range.1 hj
        use k - j
        constructor
        · -- Show (k - j) ∈ Ico 1 (k + 1)
          omega
        · -- Show k - (k - j) = j
          exact Finset.mem_Ico.mpr (by omega)
      · -- Finally, show `p^(k - i) = p^(k - i)`
        intro i hi
        rfl

    -- 5) Chain the results together
    calc ∑ i ∈ Finset.Ico 1 (k + 1), (p ^ k) / (p ^ i)
      = ∑ i ∈ Finset.Ico 1 (k + 1), p ^ (k - i) := sum₁
      _ = ∑ j ∈ Finset.range k, p ^ j := sum₂
      _ = (p ^ k - 1) / (p - 1) := geomSum_eq h_pos k

  rw [geom_sum]
  norm_num
