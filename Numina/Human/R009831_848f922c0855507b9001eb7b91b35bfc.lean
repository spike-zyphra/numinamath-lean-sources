import Mathlib

/- Zij $n \geq 2$ een positief geheel getal en $p$ een priemgetal zodat $n \mid p-1$ en $p \mid n^{3}-1$. Bewijs dat $4 p-3$ een kwadraat is. -/
theorem number_theory_604256 (n : ℕ) (hn : 2 ≤ n) (p : ℕ) (hp : Nat.Prime p)
    (h1 : n ∣ p - 1) (h2 : p ∣ n^3 - 1) :
    IsSquare (4 * p - 3) := by

    have twolep : 2 ≤ p := by exact Nat.Prime.two_le hp

    -- p ∣ n^2 + n +1
    -- Here, we use the fact that n^3 -1 = (n-1)*(n^2+n+1) and it cannot happen that p ∣ n-1.
    have pn2pnp1 : p ∣ n^2 + n + 1 := by
      have tmp1 : n^3 - 1 = (n-1)*(n^2 + n + 1) := by
        have : 0 < n -1 := by omega
        have : 2^3 ≤ n^3 := by exact Nat.pow_le_pow_left hn 3
        have : 0 < n^3 - 1 := by omega
        qify; field_simp; ring_nf
      have tmp2 : p ∣ (n-1)*(n^2 + n + 1) := by rw [tmp1] at h2; assumption
      have : p ∣ (n-1) ∨ p ∣ (n^2+n+1) := by
        exact (Nat.Prime.dvd_mul hp).mp tmp2
      have : ¬ p ∣ (n-1) := by
        by_contra pdnm1
        have : n ≤ p-1 := by apply Nat.le_of_dvd; omega; exact h1
        have : n-1 ≤ p-2 := by omega
        have : p ≤ n-1 := by apply Nat.le_of_dvd; omega; exact pdnm1
        have : p ≤ p-2 := by linarith
        omega
      tauto

    -- let p = kn+1. We prove that k has to be n-1.
    obtain ⟨k, hk⟩ := h1
    have onelek : 1 ≤ k := by
      by_contra kl1; push_neg at kl1;
      have keq0 : k = 0 := by exact Nat.lt_one_iff.mp kl1
      rw [keq0] at hk; ring_nf at hk; omega
    have peq : p = k*n + 1 := by rw[mul_comm]; rw [← hk]; exact Eq.symm (Nat.succ_pred_prime hp)

    have keqnp1: k = n + 1 := by
      have : ¬ n+1 < k := by
        by_contra np1lk
        have : 0 < k - n - 1 := by omega

        have lem : (k * n+1) ∣ (k-n-1) := by
          have tmp1: (k*n+1) ∣ (n^2 + n + 1) := by rw [← peq]; assumption
          have tmp2: (k*n+1) ∣ k * (n^2 + n + 1) := by exact Dvd.dvd.mul_left tmp1 k
          have tmp3: (k*n+1) ∣ (k*n+1) := by exact Nat.dvd_refl (k * n + 1)
          have tmp4: (k*n+1) ∣ (n+1)*(k*n+1) := by exact Nat.dvd_mul_left (k * n + 1) (n + 1)
          have : (k*n+1) ∣ (k * (n^2 + n + 1)) - ((n+1)*(k*n+1)) := by exact Nat.dvd_sub' tmp2 tmp4
          have : k-n-1 = (k * (n^2 + n + 1)) - ((n+1)*(k*n+1)) := by qify; field_simp; ring_nf; omega
          rw [this]; assumption

        have : k*n + 1 ≤ k -n - 1 := by exact Nat.le_of_dvd this lem
        have : k - n - 1 ≤ k-3 := by omega
        have : k+1 ≤ k*n+1 := by nlinarith
        have : k+1 ≤ k-3 := by linarith
        omega
      have : ¬ k < n+1 := by
        by_contra klnp1
        have np1mkpos: 0 < n+1-k := by omega
        have knp1div: k*n + 1 ∣ n+1 - k := by
          have tmp1: (k*n+1) ∣ (n^2 + n + 1) := by rw [← peq]; assumption
          have tmp2: (k*n+1) ∣ k * (n^2 + n + 1) := by exact Dvd.dvd.mul_left tmp1 k
          have tmp3: (k*n+1) ∣ (k*n+1) := by exact Nat.dvd_refl (k * n + 1)
          have tmp4: (k*n+1) ∣ (n+1)*(k*n+1) := by exact Nat.dvd_mul_left (k * n + 1) (n + 1)
          have : (k*n+1) ∣ ((n+1)*(k*n+1)) - (k * (n^2 + n + 1)) := by exact Nat.dvd_sub' tmp4 tmp2
          have : n+1 - k = ((n+1)*(k*n+1)) - (k * (n^2 + n + 1)) := by qify; field_simp; ring_nf; omega
          rw [this]; assumption

        have : k*n+1 ≤ n+1 - k := by exact Nat.le_of_dvd np1mkpos knp1div
        have : n ≤ k * n := by nlinarith
        have : n+1 ≤ k*n + 1 := by linarith
        have : n+1 ≤ n+1 - k := by linarith
        omega

      linarith

    -- Since k = n-1, we have p = n^2 + n + 1.
    have peq: p = n^2 + n + 1 := by
      have tmp1 : p = n*k + 1 := by rw [← hk]; exact Eq.symm (Nat.succ_pred_prime hp)
      rw [tmp1]; rw [keqnp1]; ring

    -- Then, 4p-3 = (2n+1)^2.
    use (2*n+1)
    rw[peq]; ring_nf; omega
