import Mathlib

/-1. $\mathbf{N} \mathbf{1}(\mathbf{T W N}){ }^{\mathrm{IMO}+4}$ Find all pairs of positive integers $(x, p)$ such that $p$ is a prime, $x \leq 2 p$, and $x^{p-1}$ is a divisor of $(p-1)^{x}+1$.-/
theorem other_24886 (x p : ℕ) (xpos : 0 < x) (hp : p.Prime) :
(x ≤ 2 * p ∧ x ^ (p - 1) ∣ (p - 1) ^ x + 1) ↔ x = 1 ∨ (x = 2 ∧ p = 2) ∨ (x = 3 ∧ p = 3):= by
  have pge := hp.two_le
  have : Fact (p.Prime) := ⟨hp⟩
  constructor
-- First prove that if we assume $x$ is less than $4$, then we will get all the results in the final goal
  · rintro ⟨hl, hr⟩; by_cases h : x < 4
  -- Split to the cases when $x$ is $1$, $2$ or $3$. The case $x=1$ is trivial
    · interval_cases x; simp_all
    -- For the case $x=2$, we prove that if $p$ is not $2$, we will get a contradiction on the parity of $(p-1)^2+1$
      · by_cases h'' : p ≠ 2
        · obtain ⟨k, hk⟩ : Odd p := Nat.Prime.odd_of_ne_two hp h''
          have : Even ((p - 1) ^ 2 + 1) := by
            rw [Nat.even_iff]; apply Nat.mod_eq_zero_of_dvd; apply Nat.dvd_trans _ hr
            apply Nat.dvd_of_pow_dvd (show 1≤p-1 by rw [Nat.le_sub_one_iff_lt]; any_goals linarith)
            rfl
          rw [← Nat.not_odd_iff_even] at this
          suffices : Odd ((p - 1) ^ 2 + 1); contradiction
          use 2 * k ^ 2; rw [hk, Nat.add_sub_cancel]; ring
        push_neg at h''; simp; assumption
    -- For the case $x=3$, we first prove that $p$ is greater or equal to $3$
      replace pge : 3 ≤ p := by
        by_contra!; replace this : p = 2 := by linarith
        simp_all; contradiction
    -- Apply various properties of prime numbers and divisions in Nat, we can prove that $3$ divides $p$, therefore they must be equal.
      simp; symm; rw [← Nat.prime_dvd_prime_iff_eq]
      rw [← Prime.dvd_pow_iff_dvd (show _ by rw [← Nat.prime_iff]; norm_num) (show 3≠0 by simp)]
      have tmph1 : p ^ 3 = (p - 1) ^ 3 + 1 + 3 * (p ^ 2 - p) := by
        zify; repeat rw [Nat.cast_sub]; push_cast
        ring; apply Nat.le_self_pow; simp; linarith
      rw [tmph1]; apply Nat.dvd_add; apply Nat.dvd_trans _ hr
      rw [Nat.dvd_prime_pow]; use 1; constructor
      · rw [Nat.le_sub_one_iff_lt]; any_goals linarith
      any_goals simp
      any_goals norm_num
      exact hp
  -- Assume that $x$ is greater or equal to $4$, we need to reach a contradiction
    push_neg at h; right; right
  -- Prove that the set of prime factors of $x$ is nonempty
    have xdivnem : x.primeFactors.Nonempty := by
      obtain ⟨m,hm⟩ := Nat.exists_prime_and_dvd (show x≠1 by linarith)
      use m; simp; split_ands; exact hm.left; exact hm.right
      linarith
  -- Prove that $p$ is greater or equal to $3$
    replace pge : 3 ≤ p := by
      by_contra!; replace this : p = 2 := by linarith
      simp_all; apply Nat.le_of_dvd at hr; linarith
      simp
  -- Prove that $p$ and $x$ are both odd
    have podd : Odd p := by apply hp.odd_of_ne_two; linarith
    have xodd : Odd x := by
      rw [← Nat.not_even_iff_odd]; rintro ⟨k, hk⟩
      have : Even ((p - 1) ^ x + 1) := by
        rw [Nat.even_iff]; apply Nat.mod_eq_zero_of_dvd; apply Nat.dvd_trans _ hr
        use 2 ^ (p-2) * k ^ (p - 1); rw [hk, ← two_mul, mul_pow]
        nth_rw 1 [show p-1 = p-2+1 by zify; rw [Nat.cast_sub, Nat.cast_sub]; ring; any_goals linarith]
        rw [pow_succ]; ring
      rw [← Nat.not_odd_iff_even] at this
      suffices : Odd ((p - 1) ^ x + 1); contradiction
      rcases podd with ⟨k, hk⟩; use 2 ^ (x - 1) * k ^ x
      rw [hk, Nat.add_sub_cancel, mul_pow]; nth_rw 1 [show x=x-1+1 by rw [Nat.sub_add_cancel]; linarith]
      rw [pow_succ]; ring
  -- let $q$ be the smallest prime factor of $x$, prove some basic properties about $q$
    let q := x.primeFactors.min' xdivnem
  -- Prove that for any prime factor $r$ of $x$, $q$ has to be less or equal to $r$
    have qmin : ∀ r ∈ x.primeFactors, q ≤ r := by
      intro r hr; simp only [q]; exact Finset.min'_le x.primeFactors r hr
  -- Prove that $q$ is prime and $q$ divide x
    have qdvd : q.Prime ∧ q ∣ x := by
      suffices : q ∈ x.primeFactors
      · simp at this; constructor
        exact this.left; exact this.right.left
      simp only [q]; exact Finset.min'_mem x.primeFactors xdivnem
  -- Prove that $q$ is odd
    have qodd : Odd q := by
      apply qdvd.left.odd_of_ne_two; intro h'
      rw [← Nat.not_even_iff_odd] at xodd; suffices : Even x; contradiction
      rw [h'] at qdvd; rw [Nat.even_iff]; apply Nat.mod_eq_zero_of_dvd
      exact qdvd.right
  -- Prove that $q$ is greater or equal to $3$
    have qge : 3 ≤ q := by
      by_contra!; have := qdvd.left.two_le
      replace this : q = 2 := by linarith
      rw [this] at qodd; contradiction
  -- Prove that $p-1$ and $q$ are coprime
    have ps1copr : (p - 1).Coprime q := by
      rw [Nat.coprime_comm]; cases Nat.coprime_or_dvd_of_prime qdvd.left (p-1)
      · assumption
      rename_i h'; rw [← Prime.dvd_pow_iff_dvd (show Prime q by rw [← Nat.prime_iff]; exact qdvd.left) (show x≠0 by linarith)] at h'
      suffices : q ∣ (p - 1) ^ x + 1
      · have := Nat.dvd_sub (show (p-1)^x ≤ (p-1)^x+1 by simp) this h'
        rw [add_comm, Nat.add_sub_cancel] at this; apply Nat.le_of_dvd at this
        any_goals linarith
      apply Nat.dvd_trans _ hr; rw [Prime.dvd_pow_iff_dvd]; exact qdvd.right
      rw [← Nat.prime_iff]; exact qdvd.left
      intro h'; rw [Nat.sub_eq_zero_iff_le] at h'; linarith
  -- In order to properly use Mathlib results on ZMod, we need the following two simple facts
    have : NeZero (q - 1) := by
      rw [neZero_iff]; intro h'
      rw [Nat.sub_eq_zero_iff_le] at h'
      have := qdvd.left.two_le; linarith
    have : Fact (1 < q - 1) := by
      rw [fact_iff, Nat.lt_sub_iff_add_lt]; simp; linarith
  -- Prove that there exists $a$ and $b$ such that $xa$ equals $(q-1)b+1$
    obtain ⟨a, b, ⟨apos, bpos, hab⟩⟩ : ∃ a b, 0 < a ∧ 0 < b ∧ x * a = (q - 1) * b + 1 := by
    -- Rewrite the goal as a division relation
      suffices : ∃ a, 0 < a ∧ q - 1 ∣ x * a - 1
      · rcases this with ⟨a, ⟨apos, ⟨b, hb⟩⟩⟩; use a; use b; split_ands
        · exact apos
        · by_contra!; simp_all; rw [Nat.sub_eq_zero_iff_le] at hb
          have : 1 * 1 < x * a := by apply mul_lt_mul; any_goals linarith
          linarith
        rw [← Nat.sub_eq_iff_eq_add]; exact hb
        rw [show 1=1*1 by simp]; apply mul_le_mul; any_goals linarith
    -- Assuming $x$ is coprime to $q-1$, prove the division relation by applying properties of ZMod and units
      suffices : x.Coprime (q-1)
      · rw [← ZMod.isUnit_iff_coprime] at this
        apply IsUnit.exists_right_inv at this; rcases this with ⟨w, hw⟩
        use w.val; constructor
        · by_contra!; simp_all
        let h'w := hw
        rw [← ZMod.natCast_zmod_val w, ← Nat.cast_mul, ZMod.natCast_eq_iff, ZMod.val_one] at h'w
        rcases h'w with ⟨k, hk⟩; rw [← Nat.sub_eq_iff_eq_add'] at hk
        simp [hk]; by_contra!; simp at this
        cases this; any_goals simp_all
    -- Prove by contradiction, if $x$ is not coprime to $q-1$, then their gcd has to be greater or equal to $2$
      rw [Nat.coprime_iff_gcd_eq_one]; by_contra!
      replace this : 2 ≤ x.gcd (q - 1) := by
        have := Nat.gcd_pos_of_pos_left (q - 1) (show 0 < x by linarith)
        by_contra!; replace this : x.gcd (q - 1) = 1 := by linarith
        contradiction
      obtain ⟨r, ⟨hr1, hr2⟩⟩ := Nat.exists_prime_and_dvd (show x.gcd (q-1)≠1 by linarith)
      have tmph1 : r ∈ x.primeFactors ∧ r < q := by
        simp; split_ands; exact hr1
        · apply Nat.dvd_trans hr2; exact Nat.gcd_dvd_left x (q - 1)
        · linarith
        apply Nat.le_of_dvd at hr2
        have : x.gcd (q - 1) < q := by
          suffices : q - 1 < q
          · have : x.gcd (q - 1) ≤ q - 1 := by
              apply Nat.gcd_le_right; rw [Nat.lt_sub_iff_add_lt]; linarith
            linarith
          exact Nat.sub_one_lt_of_lt qge
        linarith; apply Nat.gcd_pos_of_pos_left; linarith
      have := qmin r tmph1.left; linarith
  -- Assuming that $q$ is equal to $p$, prove that $x$ is equal to $p$ because of hl, then find a contradiction by computing padicValNat $p$ $(p-1)^p+1$ :
  -- on one hand by hr, it has to be larger than $p-1$; on the other hand by padicValNat.pow_add_pow, it equals $2$
    suffices : q = p
    · rw [this] at qdvd
      obtain ⟨k, hk⟩ := qdvd.right; rw [hk, mul_comm, mul_le_mul_right] at hl
      interval_cases k; simp_all
      · simp [hk] at hr; rw [padicValNat_dvd_iff_le] at hr
        suffices : padicValNat p ((p - 1) ^ p + 1) = 2
        · rw [this, Nat.sub_le_iff_le_add] at hr; linarith
        nth_rw 2 [show 1 = 1 ^ p by simp]
        rw [padicValNat.pow_add_pow, Nat.sub_add_cancel]; simp
        linarith; assumption
        rw [Nat.sub_add_cancel]; linarith
        intro h'; apply Nat.le_of_dvd at h'; suffices : p - 1 < p; linarith
        exact Nat.sub_one_lt_of_lt pge
        simp; linarith; assumption; simp
      rw [hk, mul_comm, ← Nat.not_even_iff_odd] at xodd; simp at xodd
      linarith
  -- It only remains to prove that $q$ is equal to $p$, for this we prove $q$ divides $p$
    rw [← Nat.prime_dvd_prime_iff_eq, show p = p-1+1 by rw [Nat.sub_add_cancel]; linarith]
    rw [← Nat.modEq_zero_iff_dvd, show p-1 = (p-1)*1 by simp]
  -- Apply Fermat-Euler totient theorem to prove the following auxillary lemma
    have tmph1 : (p - 1) * 1 + 1 ≡ (p - 1) * (p - 1) ^ ((q - 1) * b) + 1 [MOD q] := by
      apply Nat.ModEq.add; apply Nat.ModEq.mul; rfl
      rw [pow_mul]; nth_rw 1 [show 1 = 1^b by simp]; apply Nat.ModEq.pow
      rw [show q-1 = q.totient by rw [Nat.totient_prime]; exact qdvd.left, Nat.ModEq.comm]
      exact Nat.ModEq.pow_totient ps1copr; rfl
  -- Apply the hypothesis hab and various properties of Nat.ModEq and Nat division to finish the goal
    apply Nat.ModEq.trans tmph1; rw [← pow_succ', ← hab, Nat.modEq_zero_iff_dvd]
    rw [pow_mul]; nth_rw 2 [show 1 = 1^a by simp]
    have tmph2 : (p - 1) ^ x + 1 ∣ ((p - 1) ^ x) ^ a + 1 ^ a := by
      apply Odd.nat_add_dvd_pow_add_pow; suffices : Odd (x * a)
      · rw [Nat.odd_mul] at this; exact this.right
      rw [hab, add_comm]; apply Odd.add_even; simp
      rw [Nat.even_mul]; left; rcases qodd with ⟨k, hk⟩; use k
      rw [hk, Nat.add_sub_cancel, two_mul]
    apply Nat.dvd_trans _ tmph2; apply Nat.dvd_trans _ hr
    rw [Prime.dvd_pow_iff_dvd]; exact qdvd.right
    rw [← Nat.prime_iff]; any_goals exact qdvd.left
    intro h'; rw [Nat.sub_eq_zero_iff_le] at h'; linarith; exact hp
-- Conversely, it is straightforward to check that all the cases listed in the assumption satisfies the goal
  intro h; rcases h with h|h|h; any_goals simp_all
  linarith
