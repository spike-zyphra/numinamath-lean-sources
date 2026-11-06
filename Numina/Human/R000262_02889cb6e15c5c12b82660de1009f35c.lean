import Mathlib

/- Positive integers  $ a < b$  are given.
Prove that among every  $ b$  consecutive positive integers
there are two numbers whose product is divisible by  $ ab$ . -/
theorem number_theory_8737 {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a < b) (n : ℕ) :
    ∃ c d, c ∈ Finset.Ico n (n + b) ∧ d ∈ Finset.Ico n (n + b) ∧
    c ≠ d ∧ a * b ∣ c * d := by
  -- Obviously among  $b$  consecutive positive integers there are two numbers
  -- $p$  which is divisible by  $a$  and
  -- $q$  which is divisible by  $b$ .
  have a_dvd_p : ∃ p, p ∈ Finset.Ico n (n + b) ∧ a ∣ p := by
    by_cases han : a ∣ n
    . use n
      simp [hb, han]
    use n + a - n % a
    have han1 : n ≤ n + a - n % a := by
      rw [Nat.add_sub_assoc]
      apply Nat.le_add_right
      exact (Nat.mod_lt _ ha).le
    have han2 : n + a - n % a < n + b := by
      trans n + a
      suffices 0 < n % a by
        rw [← Nat.add_lt_add_iff_right (k := n % a), Nat.sub_add_cancel]
        exact Nat.lt_add_of_pos_right this
        . trans a
          . exact (Nat.mod_lt _ ha).le
          . exact Nat.le_add_left a n
      rw [Nat.pos_iff_ne_zero]
      intro hna
      rw [Nat.dvd_iff_mod_eq_zero] at han
      contradiction
      . linarith
    have han3 : a ∣ n + a - n % a := by
      use (n / a + 1)
      have := Nat.div_add_mod n a
      nth_rw 1 [← this]
      ring_nf
      rw [Nat.add_sub_cancel]
    simp [han1, han2, han3]
  have b_dvd_q : ∃ q, q ∈ Finset.Ico n (n + b) ∧ b ∣ q := by
    by_cases hbn : b ∣ n
    . use n
      simp [hb, hbn]
    use n + b - n % b
    have hbn1 : n ≤ n + b - n % b := by
      rw [Nat.add_sub_assoc]
      apply Nat.le_add_right
      exact (Nat.mod_lt _ hb).le
    have hbn2 : n + b - n % b < n + b := by
      suffices 0 < n % b by
        rw [← Nat.add_lt_add_iff_right (k := n % b), Nat.sub_add_cancel]
        exact Nat.lt_add_of_pos_right this
        . trans b
          . exact (Nat.mod_lt _ hb).le
          . exact Nat.le_add_left b n
      rw [Nat.pos_iff_ne_zero]
      intro hnb
      rw [Nat.dvd_iff_mod_eq_zero] at hbn
      contradiction
    have hbn3 : b ∣ n + b - n % b := by
      use (n / b + 1)
      have := Nat.div_add_mod n b
      nth_rw 1 [← this]
      ring_nf
      rw [Nat.add_sub_cancel]
    simp [hbn1, hbn2, hbn3]
  rcases a_dvd_p with ⟨p, hp⟩
  rcases b_dvd_q with ⟨q, hq⟩
  rcases eq_or_ne p q with p_eq_q | p_ne_q
  swap
  -- **Case1:** $p\neq q$ Then  $ab|pq$ ,and the proof is completed.
  use p, q
  split_ands
  . exact hp.1
  . exact hq.1
  . exact p_ne_q
  . exact mul_dvd_mul hp.2 hq.2
  -- **Case2:**  $p=q$ Then  $lcm(a,b)|p$ .
  have hap : a ∣ p := hp.2
  have hbp : b ∣ p := p_eq_q ▸ hq.2
  have habp : a.lcm b ∣ p := Nat.lcm_dvd hap hbp
  -- Since  $gcd(a,b)\le \frac{1}{2}b$ ,
  have : a.gcd b ≤ a := by
    apply Nat.le_of_dvd ha
    apply Nat.gcd_dvd_left
  have : a.gcd b < b := by linarith
  -- there are at least two numbers which are divisible by  $gcd(a,b)$ .
  -- Then ∃ $x\neq p$  s.t.  $gcd(a,b)|x$ .
  have habx : ∃ x ∈ Finset.Ico n (n + b), p ≠ x ∧ a.gcd b ∣ x := by
    set s : Finset ℕ := ((Finset.Ico n (n + b)).filter (a.gcd b ∣ ·)) with hs
    have p_mem_s : p ∈ s := by
      rw [hs, Finset.mem_filter]
      refine ⟨hp.1, ?_⟩
      trans a.lcm b
      . trans a
        . exact Nat.gcd_dvd_left a b
        . exact Nat.dvd_lcm_left a b
      . exact habp
    set x1 := if a.gcd b ∣ n then n else n + a.gcd b - n % a.gcd b with hx1
    set x2 := if a.gcd b ∣ n then n + a.gcd b else n + a.gcd b - n % a.gcd b + a.gcd b with hx2
    -- have hbn3 : b ∣ n + b - n % b := by
    --   use (n / b + 1)
    --   have := Nat.div_add_mod n b
    --   nth_rw 1 [← this]
    --   ring_nf
    --   rw [Nat.add_sub_cancel]
    have gcd_dvd_x1 : a.gcd b ∣ x1 := by
      rw [hx1]
      split
      . assumption
      use (n / a.gcd b + 1)
      have := Nat.div_add_mod n (a.gcd b)
      nth_rw 1 [← this]
      ring_nf
      rw [Nat.add_sub_cancel]
    have gcd_dvd_x2 : a.gcd b ∣ x2 := by
      rw [hx2]
      split
      . exact Dvd.dvd.add (by assumption) (by exact Nat.dvd_refl (a.gcd b))
      use (n / a.gcd b + 2)
      have := Nat.div_add_mod n (a.gcd b)
      nth_rw 1 [← this]
      ring_nf
      rw [Nat.add_sub_cancel]
      ring
    have x1_mem_Ico : x1 ∈ Finset.Ico n (n + b) := by
      rw [hx1]
      split
      . simp [hb]
      simp
      constructor
      . have : 0 < a.gcd b := by
          rw [Nat.pos_iff_ne_zero]
          exact Nat.gcd_ne_zero_left ha.ne'
        have : n % a.gcd b < a.gcd b := by
          apply Nat.mod_lt
          assumption
        omega
      omega
    have x2_mem_Ico : x2 ∈ Finset.Ico n (n + b) := by
      rw [hx2]
      split
      . simp; omega
      simp
      constructor
      . have : 0 < a.gcd b := by
          rw [Nat.pos_iff_ne_zero]
          exact Nat.gcd_ne_zero_left ha.ne'
        have : n % a.gcd b < a.gcd b := by
          apply Nat.mod_lt
          assumption
        omega
      have : a.gcd b ∣ b := Nat.gcd_dvd_right _ _
      rcases this with ⟨k, hk⟩
      have : 2 ≤ k := by
        by_contra h
        push_neg at h
        interval_cases k
        rw [mul_zero] at hk
        linarith
        rw [mul_one] at hk
        linarith
      have : 2 * a.gcd b ≤ a.gcd b * k := by nlinarith
      rw [← hk] at this
      omega
    have x1_mem_s : x1 ∈ s := by
      rw [hs, Finset.mem_filter]
      exact ⟨x1_mem_Ico, gcd_dvd_x1⟩
    have x2_mem_s : x2 ∈ s := by
      rw [hs, Finset.mem_filter]
      exact ⟨x2_mem_Ico, gcd_dvd_x2⟩
    have x1_ne_x2 : x1 ≠ x2 := by
      rw [hx1, hx2]
      have : a.gcd b ≠ 0 := Nat.gcd_ne_zero_left ha.ne'
      split <;> simpa
    have pair_subset_s : {x1, x2} ⊆ s := by
      rw [Finset.subset_iff]
      intro x hx
      simp at hx
      rcases hx with rfl | rfl <;> assumption
    have two_le_card : 2 ≤ s.card := by
      rw [← Finset.card_pair x1_ne_x2]
      exact Finset.card_le_card pair_subset_s
    have := Finset.card_erase_add_one p_mem_s
    have : 0 < (s.erase p).card := by omega
    rw [Finset.card_pos] at this
    rcases this with ⟨x, hx⟩
    use x
    simp [s] at hx ⊢
    exact ⟨by exact hx.2.1, by rw [eq_comm]; exact hx.1, by exact hx.2.2⟩
  -- Therefore  $ab=lcm(a,b)gcd(a,b)|px$ ,and the proof is completed.
  rcases habx with ⟨x, hx⟩
  use p, x
  split_ands
  . exact hp.1
  . exact hx.1
  . exact hx.2.1
  . rw [← Nat.gcd_mul_lcm a b, mul_comm]
    exact mul_dvd_mul habp hx.2.2
  -- From case $1,2$ ,completing the proof.
