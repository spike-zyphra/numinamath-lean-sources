import Mathlib

/- A positive integer $n$ does not divide $2^{a} 3^{b}+1$ for any positive integers $a$ and $b$. Prove that $n$ does not divide $2^{c}+3^{d}$ for any positive integers $c$ and $d$. -/
theorem number_theory_604483 (n : ℕ) (hn : n ≠ 0) (h : ∀ a b : ℕ, a > 0 → b > 0 → ¬(n ∣ 2^a * 3^b + 1)) :
    ∀ c d : ℕ, c > 0 → d > 0 → ¬(n ∣ 2^c + 3^d) := by 
    --Assume the contrary: 
    by_contra h1
    --$n$ divides $2^{c}+3^{d}$. 
    push_neg at h1
    obtain ⟨c, d, hc, hd, hn'⟩ := h1
    absurd h
    push_neg
    --Clearly $n$ is not divisible by 3;
    have h2 : ¬ 3 ∣ n := by
      by_contra h21
      have h22 : 3 ∣ 2 ^ c + 3 ^ d := by
        exact Nat.dvd_trans h21 hn'
      have h23 : 3 ∣ 3 ^ d := by
        use 3 ^ (d - 1)
        have : 3 = 3 ^ 1 := by norm_num
        nth_rw 2 [this]
        exact Eq.symm (pow_mul_pow_sub 3 hd)
      have h24 : 3 ∣ 2 ^ c := by
        exact (Nat.dvd_add_iff_left h23).mpr h22
      have h25 : Nat.Coprime 3 (2 ^ c) := by
        exact Nat.Coprime.pow_right c rfl
      have h26 : 2 ^ c = 1 * 2 ^ c := by rw [one_mul]
      rw [h26] at h24
      have h27 : 3 ∣ 1 := by
        exact Nat.Coprime.dvd_of_dvd_mul_right h25 h24
      norm_num at h27
    --therefore $n$ divides $3^{k}-1$ for some $k$.
    have h3 : ∃ (k : ℕ), (k > 0) ∧ n ∣ (3 ^ k - 1) := by
      use Nat.totient n
      constructor
      · simp only [gt_iff_lt, Nat.totient_pos]
        exact Nat.zero_lt_of_ne_zero hn
      · have h31 : 3 ^ (Nat.totient n) ≡ 1 [MOD n] := by
          have h32 : Nat.Coprime 3 n := by
            have : Nat.Prime 3 := by norm_num
            exact (Nat.Prime.coprime_iff_not_dvd this).mpr h2
          exact Nat.ModEq.pow_totient h32
        unfold Nat.ModEq at h31
        apply Nat.dvd_of_mod_eq_zero 
        exact Nat.sub_mod_eq_zero_of_mod_eq h31
    obtain ⟨k, ⟨hk1, hk2⟩⟩ := h3
    --Choosing $s$ so that $k s&gt;d$
    have h4 : ∃ (s : ℕ), (s > 0) ∧ k * s > d := by
      use d + 1
      constructor
      · exact Nat.add_pos_left hd 1
      · calc
          _ ≥ 1 * (d + 1) := by
            exact Nat.mul_le_mul_right (d + 1) hk1
          _ = d + 1 := by 
            rw [one_mul]
          _ > d := by 
            simp only [gt_iff_lt, lt_add_iff_pos_right, zero_lt_one]
    obtain ⟨s, ⟨hs1, hs2⟩⟩ := h4
    use c
    use k * s - d
    constructor
    · exact hc
    · constructor
      · exact Nat.zero_lt_sub_of_lt hs2
      · --we see that $n$ divides $3^{k s-d}\left(2^{c}+3^{d}\right)=2^{c} 3^{k s-d}+3^{k s}$.
        have h5 : 3 ^ (k * s - d) * (2 ^ c + 3 ^ d) = 2 ^ c * 3 ^ (k * s - d) + 3 ^ (k * s) := by
          have : 3 ^ (k * s - d) * 3 ^ d = 3 ^ (k * s) := by
            rw [← pow_add]
            congr
            omega
          rw [mul_add, this]
          nth_rw 1 [mul_comm]
        have h6 : n ∣ 2 ^ c * 3 ^ (k * s - d) + 3 ^ (k * s) := by 
          rw [← h5]
          have : Nat.Coprime n (3 ^ (k * s - d)) := by
            apply Nat.Prime.coprime_pow_of_not_dvd
            norm_num
            exact h2
          exact (Nat.Coprime.dvd_mul_left this).mpr hn'
        --Then $n$ also divides $2^{c} 3^{k s-d}+1=2^{c} 3^{k s-d}+3^{k s}-\left(3^{k s}-1\right)$, a contradiction.
        have h7 : 2 ^ c * 3 ^ (k * s - d) + 1 = 2 ^ c * 3 ^ (k * s - d) + 3 ^ (k * s) - (3 ^ (k * s) - 1) := by
          have : 1 = 3 ^ (k * s) - (3 ^ (k * s) - 1) := by  
            apply Eq.symm (Nat.sub_sub_self _)
            exact Nat.one_le_pow' (k * s) 2
          nth_rw 1 [this]
          apply Eq.symm (Nat.add_sub_assoc _ (2 ^ c * 3 ^ (k * s - d)))
          simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]
        rw [h7]
        apply Nat.dvd_sub' h6 
        have h8 : 3 ^ k - 1 ∣ 3 ^ (k * s) - 1 := by
          exact nat_pow_one_sub_dvd_pow_mul_sub_one 3 k s
        exact Nat.dvd_trans hk2 h8