import Mathlib

/- Given $n$ pairwise coprime numbers, greater than 1 and less than $(2 n-1)^{2}$. Prove that among them there must be a prime number.

# -/
theorem number_theory_206846 (n : ℕ) (hn : 1 < n) (a : Fin n → ℕ)
    (ha : ∀ i, a i > 1) (hcoprime : ∀ i j, i ≠ j → Nat.Coprime (a i) (a j))
    (h : ∀ i, a i < (2 * n - 1) ^ 2) :
    ∃ i, Nat.Prime (a i) := by
    -- Assume the opposite. i.e. $Let a_1, a_2, \dots, a_n$ be pairwise coprime composite numbers
    by_contra h_no_primes
    push_neg at h_no_primes
    -- Theorems in Mathlib typically involve functions from ℕ to ℕ, and not from Fin n to ℕ, so we extend a to ℕ
    let a_ext: ℕ → ℕ := λ i ↦ if hi: i < n then a { val := i, isLt := hi } else 0
    -- Denote by $p_i$ the smallest prime divisor of the number $a_i$.
    let p := Nat.minFac ∘ a_ext
    let f: ℕ ↪ ℕ := {
      toFun := λ m ↦ if m = 0 then 2 else 2 * m + 1
      inj' := by
        intro a b h_eq
        by_cases ha: a = 0 <;> by_cases hb: b = 0
        rw [ha, hb]
        all_goals simp [ha, hb] at h_eq
        assumption
    }
    -- The numbers $\{2, 3, 5, 7, \dots, 2n - 3\}$
    let S := Finset.map f (Finset.range (n - 1))
    -- Each a_i is larger than 1, and so has a smallest prime divisor
    have h_pi_prime: ∀ i < n, Nat.Prime (p i) := by
      intro i i_bound
      apply Nat.minFac_prime
      simp [a_ext, i_bound]
      exact ne_of_gt (ha { val := i, isLt := i_bound })
    -- Then $a_i = p_i q_i$ where $p_i \le q_i$. Since $a_i < (2n - 1)^2$, it follows that $p_i < 2n - 1$.
    have h_pi_ineq: ∀ i < n, p i < 2 * n - 1 := by
      intro i i_bound
      apply (sq_lt_sq₀ _ _).mp
      let i_fin: Fin n := { val := i, isLt := i_bound }
      calc
        (p i)^2 = (Nat.minFac (a i_fin))^2 := by
          simp [p, a_ext, i_bound]
        _ ≤ a i_fin := by
          apply Nat.minFac_sq_le_self
          have := ha i_fin
          positivity
          exact h_no_primes i_fin
        _ < (2 * n - 1)^2 := h i_fin
      all_goals positivity
    -- All $p_i$ are contained among the numbers $\{2, 3, 5, 7, \dots, 2n - 3\}$
    have p_elem: ∀ i < n, p i ∈ S := by
      intro i i_bound
      rw [Finset.mem_map]
      by_cases h: p i = 2
      use 0
      constructor
      exact Finset.mem_range.mpr (tsub_pos_iff_lt.mpr hn)
      rw [h]
      rfl
      have pi_prime := h_pi_prime i i_bound
      obtain ⟨b, hb⟩ := Nat.Prime.odd_of_ne_two pi_prime h
      use b
      constructor
      apply Finset.mem_range.mpr
      have := h_pi_ineq i i_bound
      omega
      by_cases hb_zero: b = 0
      rw [hb_zero] at hb
      rw [hb] at pi_prime
      have := pi_prime.ne_one
      contradiction
      simp [f, hb_zero]
      exact Eq.symm hb
    -- Moreover, the numbers $p_1, p_2, \dots, p_n$ are distinct, as the numbers $a_1, a_2, \dots, a_n$ are pairwise coprime.
    have p_inj: ∀ i < n, ∀ j < n, p i = p j → i = j := by
      intro i i_bound j j_bound h_eq
      by_contra h_ij
      let i_fin: Fin n := { val := i, isLt := i_bound }
      let j_fin: Fin n := { val := j, isLt := j_bound }
      replace h_ij: i_fin ≠ j_fin := Fin.mk_eq_mk.ne.mpr h_ij
      -- If $p_i = p_j$ for some $i ≠ j$, then $p_i$ is a factor of both $a_i$ and $a_j$, and hence of $\gcd(a_i, a_j) = 1$.
      have h_div: ∀ k: Fin n, p k ∣ a k := by
        intro k
        rw [show a k = a_ext k from by simp [a_ext]]
        apply Nat.minFac_dvd
      have h_pi_div: p i_fin ∣ Nat.gcd (a i_fin) (a j_fin) := by
        apply Nat.dvd_gcd (h_div i_fin)
        rw [h_eq]
        exact h_div j_fin
      rw [(hcoprime i_fin j_fin h_ij).gcd_eq_one] at h_pi_div
      -- This would imply that $p_i = 1$,
      have h_pi_val: p i_fin = 1 := Nat.eq_one_of_dvd_one h_pi_div
      -- which is a contradiction since $p_i$ is prime.
      have pi_prime := h_pi_prime i i_bound
      rw [h_pi_val] at pi_prime
      exact pi_prime.ne_one (Eq.refl 1)
    -- However there are not ore than $n - 1$ prime numbers greater than $1$ and less than $2n - 1$.
    have := Finset.le_card_of_inj_on_range p p_elem p_inj
    rw [show S.card = (n - 1) from by rw [Finset.card_map, Finset.card_range]] at this
    omega