import Mathlib
open Nat

/- 60th Putnam 1999 Problem B6 X is a finite set of integers greater than 1 such that for any positive integer n, we can find m ∈ X such that m divides n or is relatively prime to n. Show that X contains a prime or two elements whose greatest common divisor is prime. -/
theorem number_theory_138530 (X : Finset ℕ) (hX : ∀ x ∈ X, x > 1)
    (hX' : ∀ n > 0, ∃ m ∈ X, m ∣ n ∨ Nat.Coprime m n) :
    ∃ p, Nat.Prime p ∧ p ∈ X ∨ ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ Nat.gcd x y = p := by
  -- There exists $n$ not coprime with any element in $X$.
  have h_exists_n : ∃ n > 0, ∀ m ∈ X, ¬ Nat.Coprime m n := by
    let n := X.prod id
    have n_pos : n > 0 := by
      apply Finset.prod_pos
      intro x hx
      exact Nat.zero_lt_of_lt (hX x hx)
    use n, n_pos
    intro m hm
    rw [Nat.coprime_iff_gcd_eq_one]
    have : m ∣ n := by
      apply Finset.dvd_prod_of_mem
      exact hm
    have h_gcd : m ∣ Nat.gcd m n := by
      exact Nat.dvd_gcd (Nat.dvd_refl m) this
    have m_gt_1 : m > 1 := hX m hm
    have m_gt_0 : m > 0 := by omega
    have gcd_mn_gt_0 : Nat.gcd m n > 0 := by
      apply Nat.gcd_pos_of_pos_left
      exact m_gt_0
    have gcd_ge_m : Nat.gcd m n ≥ m := by exact Nat.le_of_dvd gcd_mn_gt_0 h_gcd
    have gcd_gt_1 : Nat.gcd m n > 1 := by
      apply lt_of_lt_of_le m_gt_1 gcd_ge_m
    exact Nat.ne_of_gt gcd_gt_1
  -- Take the smallest $n$.
  have h_min_n : ∃ n > 0, (∀ m ∈ X, ¬ Nat.Coprime m n) ∧ ∀ k > 0, k < n → ∃ m ∈ X, Nat.Coprime m k := by
    let S := { k | k > 0 ∧ ∀ m ∈ X, ¬ Nat.Coprime m k }
    have h_n : Nat.find h_exists_n ∈ S ∧ ∀ k < Nat.find h_exists_n, k ∉ S := by
      have h_find : Nat.find h_exists_n > 0 ∧ ∀ m ∈ X, ¬ Nat.Coprime m (Nat.find h_exists_n) := Nat.find_spec h_exists_n
      constructor
      · exact h_find
      · intro k hk_lt
        intro h_k_in_S
        have : k ≥ Nat.find h_exists_n := Nat.find_le h_k_in_S
        linarith
    rcases h_n with ⟨⟨hn_pos, hn_nocoprime⟩, h_min⟩
    use Nat.find h_exists_n, hn_pos, hn_nocoprime
    intro k hk_pos hk_lt_n
    have : k ∉ S := by
      apply h_min
      exact hk_lt_n
    rw [Set.mem_setOf_eq] at this
    push_neg at this
    exact this hk_pos
  -- There exists $m ∈ X$ that divides $n$.
  rcases h_min_n with ⟨n, n_pos, hn_nocoprime, hn_min⟩
  have h_div : ∃ m ∈ X, m ∣ n := by
    rcases hX' n n_pos with ⟨m, hm, h_div_or_coprime⟩
    use m, hm
    cases h_div_or_coprime with
    | inl h => exact h
    | inr h => exfalso; exact hn_nocoprime m hm h
  -- Analyze whether $m$ is prime.
  rcases h_div with ⟨m, hm, h_m_div_n⟩
  have h_m_prime_or_not : Nat.Prime m ∨ ¬ Nat.Prime m := by
    apply em
  cases h_m_prime_or_not with
  | inl h_m_prime =>
    -- Case $1$: $m$ is prime.
    have h_conclusion : ∃ p, Nat.Prime p ∧ p ∈ X := by
      use m, h_m_prime, hm
    use m
    exact Or.inl ⟨h_m_prime, hm⟩
  | inr h_m_not_prime =>
    -- Case $2$: $m$ is not prime.
    have h_exists_p : ∃ p, Nat.Prime p ∧ p ∣ m := by
      have h_m_ne_1 : m ≠ 1 := (hX m hm).ne.symm
      rcases Nat.exists_prime_and_dvd h_m_ne_1 with ⟨p, hp_prime, hp_div_m⟩
      use p
    rcases h_exists_p with ⟨p, hp_prime, hp_div_m⟩
    -- $p$ divides $n$.
    have h_p_div_n : p ∣ n := by
      exact Nat.dvd_trans hp_div_m h_m_div_n
    -- Set $n' = n/p$, $n' < n$.
    set n' := n / p with h_n'
    have h_n_pos : n > 0 := n_pos
    have h_p_pos : p > 0 := Nat.Prime.pos hp_prime
    have h_n'_lt_n : n' < n := by
      rw [h_n']
      apply Nat.div_lt_self h_n_pos (Nat.Prime.one_lt hp_prime)
    have h_n'_pos : n' > 0 := by
      rw [h_n']
      exact Nat.div_pos (Nat.le_of_dvd h_n_pos h_p_div_n) h_p_pos
    -- There exists $m' ∈ X$ coprime with $n'$.
    have h_exists_m' : ∃ m' ∈ X, Nat.Coprime m' n' := by
      exact hn_min n' h_n'_pos h_n'_lt_n
    rcases h_exists_m' with ⟨m', hm', h_coprime_m'_n'⟩
    -- $p$ divides $m'$.
    have h_p_div_m' : p ∣ m' := by
      have h_n_eq : n = n' * p := by
        rw [h_n']
        exact Eq.symm (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero (Nat.mod_eq_zero_of_dvd h_p_div_n)))
      have h_not_coprime_m'_n : ¬ Nat.Coprime m' n := by
        exact hn_nocoprime m' hm'
      rw [h_n_eq, Nat.coprime_mul_iff_right] at h_not_coprime_m'_n
      have h_coprime_m'_p : ¬ Nat.Coprime m' p := by
        exact not_and.mp h_not_coprime_m'_n h_coprime_m'_n'
      have h_coprime_p_m' : ¬ Nat.Coprime p m' := by
        rwa [Nat.coprime_comm]
      exact (Nat.Prime.dvd_iff_not_coprime hp_prime).mpr h_coprime_p_m'
    -- $p$ is the greatest common divisor of $m$ and $m'$.
    have h_gcd_m_m'_p : Nat.gcd m m' = p := by
      -- $p$ divides both $m$ and $m'$, so $p$ is a common divisor.
      have h_p_dvd_gcd : p ∣ Nat.gcd m m' := Nat.dvd_gcd hp_div_m h_p_div_m'
      have h_gcd_dvd_m : Nat.gcd m m' ∣ m := Nat.gcd_dvd_left m m'
      have h_gcd_dvd_m' : Nat.gcd m m' ∣ m' := Nat.gcd_dvd_right m m'
      -- Use proof by contradiction: assume $g = p * d$ with $d > 1$, check for contradiction.
      by_contra h_gcd_ne_p
      have h_m_pos : m > 0 := by
        apply Nat.lt_trans
        · exact Nat.zero_lt_one
        · exact hX m hm
      have h_gcd_pos : Nat.gcd m m' > 0 := Nat.gcd_pos_of_pos_left m' h_m_pos
      have h_gcd_ge_p : Nat.gcd m m' ≥ p := Nat.le_of_dvd h_gcd_pos h_p_dvd_gcd
      have h_gcd_ne_p' : Nat.gcd m m' ≠ p := h_gcd_ne_p
      have h_gcd_gt_p : Nat.gcd m m' > p := by
        apply Nat.gt_of_not_le
        intro h_le
        apply h_gcd_ne_p'
        omega
      -- There exists $d > 1$ such that $g = p * d$.
      have h_exists_d : ∃ d > 1, Nat.gcd m m' = p * d := by
        have h_p_pos : p > 0 := Nat.Prime.pos hp_prime
        have h_gcd_div_p : (Nat.gcd m m') / p > 1 := by
          have h_gcd_pos : Nat.gcd m m' > 0 := Nat.gcd_pos_of_pos_left m' (by linarith [hX m' hm'])
          have h_gcd_gt_p : Nat.gcd m m' > p := h_gcd_gt_p
          have h_div_pos : (Nat.gcd m m') / p > 0 := Nat.div_pos (Nat.le_of_dvd h_gcd_pos h_p_dvd_gcd) h_p_pos
          have h_div_not_1 : (Nat.gcd m m') / p ≠ 1 := by
            intro h_eq
            have h_tmp : (Nat.gcd m m') / p * p = Nat.gcd m m' := Nat.div_mul_cancel h_p_dvd_gcd
            have : Nat.gcd m m' = p := by
              have h_tmp' : (Nat.gcd m m') / p = 1 := h_eq
              rw [h_tmp',one_mul] at h_tmp
              exact h_tmp.symm
            linarith [h_gcd_gt_p]
          omega
        use (Nat.gcd m m') / p
        constructor
        · exact h_gcd_div_p
        · conv_lhs => rw [← Nat.div_mul_cancel h_p_dvd_gcd]
          rw [mul_comm]
      rcases h_exists_d with ⟨d, hd_gt_1, h_gcd_eq_pd⟩
      -- If $p * d$ divides $m$ and $m'$, then it divides $n$ (since $m$ divides $n$).
      have h_pd_dvd_n : p * d ∣ n := by
        rw [← h_gcd_eq_pd]
        apply Nat.dvd_trans h_gcd_dvd_m h_m_div_n
      -- Since $n = n' * p$, $p * d$ dividing $n$ implies $d$ divides $n'$.
      have h_n_eq : n = n' * p := by
        rw [h_n']
        exact Eq.symm (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero (Nat.mod_eq_zero_of_dvd h_p_div_n)))
      have h_d_dvd_n' : d ∣ n' := by
        rw [h_n_eq] at h_pd_dvd_n
        have h_p_dvd_n : p ∣ n := h_p_div_n
        have h_p_pos : p > 0 := Nat.Prime.pos hp_prime
        have h_pd_dvd_n'p : d * p ∣ n' * p := by
          rwa [mul_comm p d] at h_pd_dvd_n
        exact (Nat.mul_dvd_mul_iff_right h_p_pos).mp h_pd_dvd_n'p
      -- Also, $p * d$ divides $m'$, so $d$ divides $m'$ (since $p$ divides $m'$).
      have h_d_dvd_m' : d ∣ m' := by
        rw [h_gcd_eq_pd] at h_gcd_dvd_m'
        exact Nat.dvd_trans (Nat.dvd_mul_left d p) h_gcd_dvd_m'
      -- But $n'$ and $m'$ are coprime, so $d$ dividing both $n'$ and $m'$ leads to a contradiction.
      have h_coprime_n'_m' : Nat.Coprime n' m' := h_coprime_m'_n'.symm
      have h_gcd_n'_m'_eq_1 : Nat.gcd n' m' = 1 := Nat.coprime_iff_gcd_eq_one.mp h_coprime_n'_m'
      have h_d_dvd_gcd_n'_m' : d ∣ Nat.gcd n' m' := Nat.dvd_gcd h_d_dvd_n' h_d_dvd_m'
      have h_d_eq_1 : d = 1 := by
        rw [h_gcd_n'_m'_eq_1] at h_d_dvd_gcd_n'_m'
        exact Nat.dvd_one.mp h_d_dvd_gcd_n'_m'
      linarith [hd_gt_1, h_d_eq_1]
    -- Verify $m ≠ m'$.
    have h_m_ne_m' : m ≠ m' := by
      intro h_eq
      rw [h_eq] at h_gcd_m_m'_p
      have : Nat.gcd m' m' = m' := Nat.gcd_self m'
      rw [this] at h_gcd_m_m'_p
      rw [h_eq] at h_m_not_prime
      have : m' = p := Nat.dvd_antisymm (by rw [h_gcd_m_m'_p]) h_p_div_m'
      rw [this] at h_m_not_prime
      contradiction
    -- Conclusion: There exist $m$, $m' ∈ X$ with $gcd(m, m') = p$.
    have h_conclusion : ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ Nat.gcd x y = p := by
      use m, hm, m', hm', h_m_ne_m', h_gcd_m_m'_p
    use p
    exact Or.inr h_conclusion
