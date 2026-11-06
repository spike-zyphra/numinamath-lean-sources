import Mathlib

theorem number_theory_133637 {S : Finset ℕ} (hSpos : ∀ n ∈ S, n > 0) (hSnonempty : S.Nonempty) :
    (∀ m ∈ S, ∀ n ∈ S, let sum := m + n; let gcd := m.gcd n; gcd ∣ sum ∧ sum / gcd ∈ S) ↔ S = {2} := by
  constructor
  . intro sum_div_gcd_in_S
    /-
    **Analysis**

    Let's start with a special case. We first learn that $2 \in S$. Then, we progressively explore other possible elements in the set $S$ and find that the set may only contain the element 2. So, how can we express this concisely?
    -/
    -- **Solution**
    -- Let $m=n$, then $2 \in S$.
    have _2_in_S : 2 ∈ S := by
      change (S : Set ℕ).Nonempty at hSnonempty
      let n := hSnonempty.some
      have n_in_S : n ∈ (S : Set ℕ) := by
        exact Set.Nonempty.some_mem hSnonempty
      simp at n_in_S
      have sum_div_gcd_2_2_in_S := sum_div_gcd_in_S n n_in_S n n_in_S
      simp at sum_div_gcd_2_2_in_S
      have : n > 0 := by
        exact hSpos n n_in_S
      simp [this] at sum_div_gcd_2_2_in_S
      exact sum_div_gcd_2_2_in_S
    have _2_dvd_of_in_S : ∀ n ∈ S, 2 ∣ n := by
      intro n n_in_S
      -- Since $S$ is a non-empty finite set, if there is an odd number $k$ in $S$, then $\frac{k+2}{(k, 2)} = k+2 \in S$. By this logic, $k+4, k+6, \cdots$ all belong to $S$, which contradicts the fact that $S$ is a finite set. Therefore, all elements in $S$ are even.
      by_contra not_2_dvd_n
      let f k := n + 2 * k
      let rec n_add_2_k_in_S : ∀ k, f k ∈ S
      | 0 => n_in_S
      | k + 1 => by
        have ih := n_add_2_k_in_S k
        have sum_div_gcd_n_add_2_k_2_in_S := sum_div_gcd_in_S (n + 2 * k) ih 2 _2_in_S
        have : n.gcd 2 = 1 := by
          have := Nat.prime_two
          rw [show n.gcd 2 = (2 : ℕ).gcd n by exact Nat.gcd_comm n 2]
          exact (Nat.Prime.coprime_iff_not_dvd this).mpr not_2_dvd_n
        simp [this] at sum_div_gcd_n_add_2_k_2_in_S
        exact sum_div_gcd_n_add_2_k_2_in_S
      have : (S : Set ℕ).Infinite := by
        set S := (S : Set ℕ)
        have range_f_subs_S : Set.range f ⊆ S := by
          intro _
          simp
          rintro k rfl
          exact n_add_2_k_in_S k
        have range_f_inf : (Set.range f).Infinite := by
          have f_inj : f.Injective := by
            simp [Function.Injective, f]
          exact Set.infinite_range_of_injective f_inj
        exact Set.Infinite.mono range_f_subs_S range_f_inf
      simp at this
    have S_erase_2_empty : S.erase 2 = ∅ := by
      set s' := S.erase 2
      -- If there are other even numbers besides 2, let's assume the smallest number other than 2 is $k$ (where $k > 2$).
      by_contra s'_ne_empty
      have s'_nonempty : s'.Nonempty := by
        exact Finset.nonempty_iff_ne_empty.mpr s'_ne_empty
      let k := s'.min' s'_nonempty
      -- not actually needed for proving `k ≠ 2` as `Finset.min'_erase_ne_self` suffices, but moved out of `k ∈ S` anyway
      have k_in_s' : k ∈ s' := by
        exact Finset.min'_mem s' s'_nonempty
      have k_in_S : k ∈ S := by
        exact Finset.mem_of_mem_erase k_in_s'
      have sum_div_gcd_k_add_2_in_S := sum_div_gcd_in_S k k_in_S 2 _2_in_S
      have _2_dvd_k := _2_dvd_of_in_S k k_in_S
      have : k.gcd 2 = 2 := by
        exact Nat.gcd_eq_right _2_dvd_k
      rw [this] at sum_div_gcd_k_add_2_in_S
      rcases sum_div_gcd_k_add_2_in_S with ⟨_, k_add_2_div_2_in_S⟩-- Then $\frac{k+2}{(k, 2)} = \frac{k}{2}+1 \in S$. And since $2 < \frac{k}{2}+1 < k$, from the previous discussion, we know that $\frac{k}{2}+1$ must be an even number. This contradicts the assumption that $k$ is the smallest number in $S$ other than 2. Therefore, $S=\{2\}$.
      -- Then $\frac{k+2}{(k, 2)} = \frac{k}{2}+1 \in S$.
      simp at k_add_2_div_2_in_S
      -- shared for both `omega`s below
      have : k ≠ 2 := by
        exact Finset.min'_erase_ne_self s'_nonempty
      -- And since $2 < \frac{k}{2}+1 < k$, from the previous discussion, we know that $\frac{k}{2}+1$ must be an even number.
      have : k / 2 + 1 < k := by
        /-
        rcases _2_dvd_k with ⟨k', k_eq_2_k'⟩
        rw [k_eq_2_k']
        simp
         -/
        have := hSpos k k_in_S
        omega
      -- This contradicts the assumption that $k$ is the smallest number in $S$ other than 2.
      have : k ≤ k / 2 + 1 := by
        --conv_rhs => unfold k
        have : k / 2 + 1 ∈ s' := by
          simp [s']
          constructor
          . omega
          . exact k_add_2_div_2_in_S
        exact Finset.min'_le s' (k / 2 + 1) this
      linarith
      -- Therefore, $S=\{2\}$.
      /-
      **Commentary**

      The extreme principle is applied here to make the expression concise.
      -/
    have : S = insert 2 (S.erase 2) := by
      exact Eq.symm (Finset.insert_erase _2_in_S)
    rw [this]
    rw [S_erase_2_empty]
    simp --rfl
  . rintro rfl
    decide
