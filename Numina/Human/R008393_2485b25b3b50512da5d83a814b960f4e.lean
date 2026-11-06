import Mathlib
set_option linter.unusedVariables false

/- Gegeven zijn positieve gehele getallen $r$ en $k$ en een oneindige rij positieve gehele getallen $a_{1} \leq a_{2} \leq \ldots$ zodat $\frac{r}{a_{r}}=k+1$. Bewijs dat er een $t$ is met $\frac{t}{a_{t}}=k$. -/
theorem number_theory_605486 (r k : ℕ) (hr : 0 < r) (hk : 0 < k)
    (a : ℕ → ℕ) (ha : ∀ i, 0 < a i) (hinc : ∀ i, a i ≤ a (i + 1))
    (h : r = (k + 1) * a r ) : ∃ t, t = k * a t := by
  -- We prove this by contradiction. Suppose such a $t$ does not exist.
  by_contra hcontra
  push_neg at hcontra
  -- First, consider the case t = k
  have h1 : a k ≥ 1 := ha k
  have h2 : k ≠ k * a k := hcontra k
  -- If $a\_{k}=1$, then $\\frac{k}{a\_{k}}=k$, contradicting our assumption.
  have h3 : a k ≠ 1 := by
    intro h_ak_eq_1
    have : k = k * a k := by
      rw [h_ak_eq_1]
      norm_num
    contradiction
  -- Therefore, $a\_{k} \\geq 2$.
  have h4 : a k ≥ 2 := by
    cases lt_or_ge (a k) 2 with
    | inl h_ak_lt_2 =>
      have : a k = 1 := by
        apply Nat.le_antisymm
        · apply Nat.le_of_lt_succ h_ak_lt_2
        · apply h1
      contradiction
    | inr h_ak_ge_2 => exact h_ak_ge_2
  -- We now prove by induction on $i$ that $a\_{i k} \\geq i+1$.
  have h_ind : ∀ i, i ≥ 1 → a (i * k) ≥ i + 1 := by
    intro i hi
    induction i with
    | zero =>
      -- $i = 0$ does not satisfy $i ≥ 1$, contradiction.
      contradiction
    | succ n n_ih =>
      -- $i = n + 1$, goal: $a ((n + 1) * k) ≥ (n + 1) + 1$
      show a ((n + 1) * k) ≥ (n + 1) + 1
      cases Nat.eq_zero_or_pos n with
      | inl h_n_zero =>
        have h_n1 : n + 1 = 1 := by rw [h_n_zero]
        have h_k : (n + 1) * k = k := by rw [h_n1]; simp
        have h_a_k : a ((n + 1) * k) = a k := by rw [h_k]
        rw [h_a_k, h_n1]
        simp
        exact h4
      | inr h_n_pos =>
        -- $n ≥ 1$.
        have h_n_ge_1 : n ≥ 1 := h_n_pos
        have h_ind_n : a (n * k) ≥ n + 1 := by
          apply n_ih h_n_ge_1
        -- Goal: $a ((n + 1) * k) ≥ (n + 1) + 1$.
        have h_step : a ((n + 1) * k) ≥ n + 1 := by
          -- Prove $a (n * k) ≤ a ((n + 1) * k)$
          have h_mono : a (n * k) ≤ a ((n + 1) * k) := by
            have h_n_succ : n + 1 = Nat.succ n := by
              rw [Nat.add_one]
            have h_n1_k : (n + 1) * k = n * k + k := by
              rw [h_n_succ,Nat.mul_comm,Nat.mul_succ,Nat.mul_comm k n]
            rw [h_n1_k]
            let motive := fun m => a (n * k) ≤ a (n * k + m)
            have : ∀ m, m ≤ k → motive m := by
              intro m hm
              induction m with
              | zero => apply Nat.le_refl
              | succ m' hm' =>
                apply Nat.le_trans (hm' (Nat.le_of_succ_le hm))
                apply hinc (n * k + m')
            apply this k (Nat.le_refl k)
          apply Nat.le_trans h_ind_n h_mono
        -- If $a ((n + 1) * k) = n + 1$, derive a contradiction.
        by_contra h_neg
        have h_eq : a ((n + 1) * k) = n + 1 := by
          apply Nat.le_antisymm
          · have : a ((n + 1) * k) < (n + 1) + 1 := Nat.lt_of_not_ge h_neg
            exact Nat.le_of_lt_succ this
          · exact h_step
        have h_t_eq : (n + 1) * k = k *  a ((n + 1) * k) := by
          rw [h_eq]
          rw [Nat.mul_comm k (n + 1)]
        have h_contra : (n + 1) * k  ≠ k * a ((n + 1) * k) := hcontra ((n + 1) * k)
        contradiction
  -- Apply induction with $i = a_r$.
  have h_ar_pos : a r ≥ 1 := ha r
  have h_r_eq : r = (k + 1) * a r := by exact h
  have h_i_ar : a r ≥ 1 := h_ar_pos
  -- By induction, $a (a_r * k) ≥ a_r + 1$.
  have h_ar_k : a (a r * k) ≥ a r + 1 := h_ind (a r) h_i_ar
  -- Since $r = (k + 1) * a_r$, we have $a_r = a (a_r * (k + 1))$.
  have h_ar_eq : a r = a (a r * (k + 1)) := by
    have h_r_eq_comm : a r * (k + 1) = r := by
      rw [Nat.mul_comm]
      exact Eq.symm h_r_eq
    rw [h_r_eq_comm]
  -- By monotonicity, $a (a_r * k) ≤ a (a_r * (k + 1))$.
  have h_monotone : a (a r * k) ≤ a (a r * (k + 1)) := by
    have h_index : a r * (k + 1) = a r * k + a r := by
      rw [Nat.mul_succ]
    rw [h_index]
    have h_aux : ∀ m, m ≤ a r → a (a r * k) ≤ a (a r * k + m) := by
      intro m hm
      induction m with
      | zero => apply Nat.le_refl
      | succ m' hm' =>
        apply Nat.le_trans (hm' (Nat.le_of_succ_le hm))
        apply hinc
    exact h_aux (a r) (Nat.le_refl (a r))
  -- Combine: $a_r = a (a_r * (k + 1)) ≥ a (a_r * k) ≥ a_r + 1$.
  have h_final : a r ≥ a r + 1 := by
    have h_trans : a r + 1 ≤ a (a r * (k + 1)) := Nat.le_trans h_ar_k h_monotone
    rw [← h_ar_eq] at h_trans
    exact h_trans
  -- Contradiction: $a_r ≥ a_r + 1 is$ impossible.
  have h_absurd : a r < a r + 1 := Nat.lt_succ_self (a r)
  have contra : False := Nat.not_le_of_lt (Nat.lt_succ_self (a r)) h_final
  exact contra
