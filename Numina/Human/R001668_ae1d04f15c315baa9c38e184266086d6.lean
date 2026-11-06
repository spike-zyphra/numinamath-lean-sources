import Mathlib

/- 4. (SWE) Let $a_{1}, a_{2}, \ldots, a_{n}, \ldots$ be a sequence of real numbers such that $0 \leq a_{n} \leq 1$ and $a_{n}-2 a_{n+1}+a_{n+2} \geq 0$ for $n=1,2,3, \ldots$. Prove that  $$ 0 \leq(n+1)\left(a_{n}-a_{n+1}\right) \leq 2 \quad \text { for } n=1,2,3, \ldots $$ -/

open Finset
theorem inequalities_25062
    (a : ℕ → ℝ)
    (h₀ : ∀ n, 0 ≤ a n ∧ a n ≤ 1)
    (h₁ : ∀ n, a n - 2 * a (n + 1) + a (n + 2) ≥ 0) 
    : ∀ n, n > 0 → (0 ≤ (n + 1) * (a n - a (n + 1)) ∧ (n + 1) * (a n - a (n + 1)) ≤ 2) := by 
  let delta : ℕ → ℝ := fun n => a n - a (n + 1)
  have ineq1 : ∀ n, delta n ≥ delta (n + 1) := by 
    intro n
    unfold delta
    obtain h1 := h₁ n
    linarith
  -- use this we could inductively prove that k ≥ n → delta k ≤ delta n
  have delta_le : ∀ m n,  m ≤ n → delta m ≥ delta n := by
    intros m n hmle
    induction' hmle with k hkin ih -- perform structural induction on the hypothesis m ≤ n
    simp
    have aux1 : delta k ≥ delta k.succ := by 
      simp
      exact ineq1 k
    linarith
  have delta_le2 : ∀ n m,  a n - a (n + m) ≤  m * delta n := by 
    intro n m
    induction m with 
    | zero => 
      simp
    | succ m ihm =>
      have aux : a n - a (n + (m + 1)) = a n - a (n + m) + delta (n + m) := by 
        unfold delta
        ring_nf
      rw [aux]
      have aux1 : delta (n + m) ≤ delta n := by 
        apply delta_le
        simp
      have aux2 : ↑(m + 1) * delta n = m * delta n + delta n := by 
        norm_num 
        ring
      rw [aux2]
      linarith
  have h1 : ∀ n, n > 0 → delta n ≥ 0 := by 
      -- - suppose that ∃ n, delta n < 0
      by_contra hc
      simp at hc
      obtain ⟨n, hn1, hn2⟩ := hc
      have aux : ∃ (M : ℕ), M * delta n < - 1:= by 
        let M1 : ℤ := (Int.floor (- 1 / delta n)) + 1
        have : M1 * delta n < - 1 := by 
          obtain aux1 := Int.lt_succ_floor (- 1 / delta n)
          have Mge : M1 > -1 / delta n := by 
            unfold M1
            exact aux1
          calc 
            _ < (-1 / delta n)* delta n := by 
              exact mul_lt_mul_of_neg_right aux1 hn2
            _ = -1 := by 
              have neq : delta n ≠ 0 := by 
                linarith
              field_simp
        have aux2 : ∃ (M : ℕ), M = M1 := by 
          have mpos : M1 > 0 := by
            unfold M1
            have aux3 : (1 / delta n) ≤  0 := by
              simp
              linarith
            have aux4 : ⌊-1 / delta n⌋ ≥ 0 := by 
              refine Int.floor_nonneg.mpr ?_
              calc 
                _ ≤ - (1 / delta n) := by 
                  linarith
                _ = _ := by 
                  ring
            linarith
          use M1.natAbs
          refine Int.natAbs_of_nonneg ?_
          linarith
        obtain ⟨M, hm⟩ := aux2
        use M
        have aux : (M : ℝ) = M1 := by 
          norm_cast
        rw [aux]
        exact this
      obtain ⟨M, hM⟩ := aux
      obtain h2 := delta_le2 n M
      have ineq_aux : a n - a (n + M) < - 1:= by 
        linarith
      have ineq_aux1 : a n - a (n + M) ≥ -1 := by 
        calc
          _ ≥ 0 - a (n + M) := by 
            obtain ⟨aux1, aux2⟩ := h₀ n 
            linarith
          _ ≥ 0 - 1 := by 
            obtain ⟨aux1, aux2⟩ := h₀ (n + M)
            linarith
          _ = -1 := by 
            simp
      linarith
  have ineq2 : ∀ n, n ≥ ∑ i ∈ Finset.Icc 1 n, (a i):= by
    intro n
    have aux : n = ∑ i ∈ Finset.Icc 1 n, 1:= by
      simp only [Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, smul_eq_mul, mul_one]
    nth_rw 1 [aux]
    have eq1 : ↑(∑ i ∈ Finset.Icc 1 n, (1 : ℕ)) = (∑ i ∈ Finset.Icc 1 n, (1 : ℝ)) := by 
      norm_cast
    rw [eq1]
    apply Finset.sum_le_sum
    intro i hi
    obtain ⟨h2, h3⟩ := h₀ i
    exact h3
  have ineq3 :∀ n,  ∑ i ∈ Finset.Icc 1 n, (a i) = n * a (n + 1) + 
    ∑ i ∈ Icc 1 n, i * delta i := by 
    intro n
    induction n with
    | zero => 
      simp
    | succ k ih => 
      have aux : ∑ i ∈ Icc 1 (k + 1), a i =  a (k + 1) + ∑ i ∈ Icc 1 k, a i := by
        have aux1 : Icc 1 (k + 1) =  insert (k + 1) (Icc 1 k) := by
          refine Eq.symm (Nat.Icc_insert_succ_right ?_)
          linarith
        rw [aux1, sum_insert]
        simp 
      rw [aux]
      have aux2 : ∑ i ∈ Icc 1 (k + 1), ↑i * delta i = (k + 1) * delta (k + 1) + ∑ i ∈ Icc 1 (k), ↑i * delta i := by 
        have aux1 : Icc 1 (k + 1) =  insert (k + 1) (Icc 1 k) := by
          refine Eq.symm (Nat.Icc_insert_succ_right ?_)
          linarith
        rw [aux1, sum_insert]
        norm_num
        simp
      rw [aux2, ih]
      have aux3 : a (k + 1) + ↑k * a (k + 1) = ↑(k + 1) * a (k + 1 + 1) 
        + (↑k + 1) * delta (k + 1) := by 
        unfold delta
        norm_num
        ring_nf
      calc 
        _ = a (k + 1) + ↑k * a (k + 1) + ∑ i ∈ Icc 1 k, ↑i * delta i := by 
          ring
        _ = _ := by 
          rw [aux3]
          norm_num
          linarith
  have ineq4 : ∀ n, n > 0 → n ≥ (n * (n + 1) / 2) * delta n := by 
    intro n npos
    calc 
      _ ≥ ∑ i ∈ Finset.Icc 1 n, (a i) := by 
        exact ineq2 _
      _ = n * a (n + 1) + ∑ i ∈ Icc 1 n, i * delta i := by 
        exact ineq3 n
      _ ≥ (∑ i ∈ Icc 1 n, (i : ℝ)) * delta n := by 
        calc 
          _ ≥ ∑ i ∈ Icc 1 n, ↑i * delta i := by 
            obtain ⟨h2, h3⟩ := h₀ (n + 1)
            have aux : ↑n * a (n + 1) ≥ 0 := by 
              positivity
            linarith
          _ ≥  (∑ i ∈ Icc 1 n, (i : ℝ)* delta n):= by
            apply sum_le_sum 
            intro i hi
            simp at hi
            obtain ⟨hi1, hi2⟩ := hi
            obtain ht := delta_le i n hi2
            apply mul_le_mul
            simp
            exact ht
            exact h1 n npos
            linarith
          _ = (∑ i ∈ Icc 1 n, (i : ℝ)) * delta n := by
            exact Eq.symm (sum_mul (Icc 1 n) Nat.cast (delta n))
      _ = _ := by 
        have aux : (∑ i ∈ Icc 1 n, (i : ℝ)) = (n * (n + 1) / 2) := by 
          
          induction n with
          | zero =>
            simp
          | succ n ih =>
            by_cases hn0 : n = 0
            rw [hn0]
            simp
            rw [Finset.sum_Icc_succ_top (by norm_num)]
            rw [ih]
            ring_nf
            field_simp
            ring_nf
            omega
        rw [aux]
  intro n npos
  constructor
  · -- first goal : 0 ≤ (↑n + 1) * (a n - a (n + 1)) 
    obtain h2 := h1 n npos
    unfold delta at h2
    positivity
  · 
    obtain h2 := ineq4 n npos
    obtain h3 := h1 n npos
    unfold delta at h2 h3
    by_contra hc
    simp at hc
    have hc1 : (↑n + 1) / 2 * (a n - a (n + 1)) > 1 := by 
      calc
        _ = (↑n + 1) * (a n - a (n + 1)) / 2 := by 
          field_simp
        _ > 2 / 2 := by 
          linarith
        _ = 1 := by 
          field_simp
    have ineq_aux : ↑n * (↑n + 1) / 2 * (a n - a (n + 1)) > n := by 
      calc 
        _ = ↑n * ((↑n + 1) / 2 * (a n - a (n + 1))) := by 
          field_simp
          ring
        _ > ↑n * 1 := by
          refine (mul_lt_mul_left ?_).mpr hc1
          norm_cast
        _ = ↑n := by simp
    linarith