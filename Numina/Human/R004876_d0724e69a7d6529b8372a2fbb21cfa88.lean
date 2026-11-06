import Mathlib
noncomputable section

-- Supplement the gcd theorem missing in Lean $4.15$.
lemma Nat.gcd_sub_mul_right_right {m n k : Nat} (h : k * m ≤ n) :
    Nat.gcd m (n - k * m) = Nat.gcd m n := by
  rw [← gcd_add_mul_right_right m (n - k * m) k, Nat.sub_add_cancel h]

-- Lemma: When $a$ is less than or equal to $k * b$, $gcd a b$ equals $gcd a (b - k * a)$.
lemma gcd_sub_multiple (a b : ℕ) (k : ℕ) (h_ka_le_b : k * a ≤ b) :
    Nat.gcd a b = Nat.gcd a (b - k * a) := by
  have h_gcd_eq : Nat.gcd a (b - k * a) = Nat.gcd a b := by
    apply Nat.gcd_sub_mul_right_right h_ka_le_b
  exact h_gcd_eq.symm

/- Gegeven is een positief geheel getal $n$. Bepaal de maximale waarde van $\operatorname{ggd}(a, b)+\operatorname{ggd}(b, c)+\operatorname{ggd}(c, a)$, onder de voorwaarde dat $a, b$ en $c$ positieve gehele getallen zijn met $a+b+c=5 n$. -/
theorem number_theory_604395 (n : ℕ) (hn : n > 0) :
    IsGreatest {x | ∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 5 * n ∧ x = Nat.gcd a b + Nat.gcd b c + Nat.gcd c a} (if 3 ∣ n then 5 * n else 4 * n) := by 
  -- Construct the set $S$.
  let S := {x | ∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 5 * n ∧ x = Nat.gcd a b + Nat.gcd b c + Nat.gcd c a}
  have h_S_nonempty : S.Nonempty := by
    exists 4 * n
    simp only [S, Set.mem_setOf_eq]
    exists n, 2 * n, 2 * n
    have h_a_pos : n > 0 := hn
    have h_b_pos : 2 * n > 0 := by linarith
    have h_c_pos : 2 * n > 0 := by linarith
    have h_sum : n + 2 * n + 2 * n = 5 * n := by ring
    have h_gcd_ab : Nat.gcd n (2 * n) = n := by
      apply Nat.gcd_eq_left
      rw [mul_comm]
      apply Nat.dvd_mul_right
    have h_gcd_bc : Nat.gcd (2 * n) (2 * n) = 2 * n := Nat.gcd_self (2 * n)
    have h_gcd_ca : Nat.gcd (2 * n) n = n := by
      apply Nat.gcd_eq_right
      rw [mul_comm]
      apply Nat.dvd_mul_right
    simp only [h_a_pos, h_b_pos, h_c_pos, h_sum, h_gcd_ab, h_gcd_bc, h_gcd_ca, true_and]
    ring
  unfold IsGreatest
  constructor
  · -- Step $1$: Define $G$ and assume $a ≤ b ≤ c$.
    by_cases h_3_div : 3 ∣ n
    · -- Case: $3 ∣ n$, $x = 5n$.
      simp only [h_3_div, S, Set.mem_setOf_eq]
      obtain ⟨k, hk⟩ := h_3_div
      exists 5 * n / 3, 5 * n / 3, 5 * n / 3
      have h_dvd: 3 ∣ n * 5 := by omega
      have h_a_pos : 5 * n / 3 > 0 := by omega
      have h_sum : 5 * n / 3 + 5 * n / 3 + 5 * n / 3 = 5 * n := by
        ring_nf
        apply Nat.div_mul_cancel
        exact h_dvd
      have h_gcd_eq : Nat.gcd (5 * n / 3) (5 * n / 3) + Nat.gcd (5 * n / 3) (5 * n / 3) + Nat.gcd (5 * n / 3) (5 * n / 3) = 5 * n := by
        rw [Nat.gcd_self]
        ring_nf
        apply Nat.div_mul_cancel
        exact h_dvd
      simp only [h_a_pos, h_sum, h_gcd_eq, true_and]
      tauto
    · -- Case: $3 ∤ n$, $x = 4n$.
      simp only [h_3_div, S, Set.mem_setOf_eq]
      exists n, 2 * n, 2 * n
      have h_a_pos : n > 0 := hn
      have h_b_pos : 2 * n > 0 := by linarith
      have h_c_pos : 2 * n > 0 := by linarith
      have h_sum : n + 2 * n + 2 * n = 5 * n := by ring
      have h_gcd_ab : Nat.gcd n (2 * n) = n := by
        apply Nat.gcd_eq_left
        rw [mul_comm]
        apply Nat.dvd_mul_right
      have h_gcd_bc : Nat.gcd (2 * n) (2 * n) = 2 * n := Nat.gcd_self (2 * n)
      have h_gcd_ca : Nat.gcd (2 * n) n = n := by
        apply Nat.gcd_eq_right
        rw [mul_comm]
        apply Nat.dvd_mul_right
      have h_gcd_eq : Nat.gcd n (2 * n) + Nat.gcd (2 * n) (2 * n) + Nat.gcd (2 * n) n = 4 * n := by
        simp only [h_gcd_ab, h_gcd_bc, h_gcd_ca]
        ring
      simp only [h_a_pos, h_b_pos, h_c_pos, h_sum, h_gcd_eq, true_and]
      tauto
  · -- Step $2$: Prove $G ≤ 5n$.
    intro x hx
    simp only [S, Set.mem_setOf_eq] at hx
    obtain ⟨a, b, c, ha, hb, hc, h_sum, h_G⟩ := hx
    -- Without loss of generality, assume $a, b, c$ are ordered, and prove the goal holds in the $a ≤ b ∧ b ≤ c$ branch.
    wlog h1 : a ≤ b generalizing a b c
    · -- Main branch: $a > b$.
      have h_b_lt_a : b < a := Nat.not_le.mp h1
      have h_gcd_symm : Nat.gcd a b + Nat.gcd b c + Nat.gcd c a = Nat.gcd b a + Nat.gcd b c + Nat.gcd c a := by
        rw [Nat.gcd_comm a b]
      rw [h_gcd_symm] at h_G
      have h_sum_symm : b + a + c = 5 * n := by
        rw [add_comm b a, h_sum]
      have h_G' : x = b.gcd a + a.gcd c + c.gcd b := by
        rw [Nat.gcd_comm c a, Nat.gcd_comm b c] at h_G
        linarith
      apply this b a c hb ha hc h_sum_symm h_G'
      linarith
    · -- Sub-branch: $a ≤ b$.
      wlog h2 : b ≤ c generalizing a b c
      · -- Main branch: $b > c$.
        have h_c_lt_b : c < b := Nat.not_le.mp h2
        by_cases h_a_ge_c : a ≥ c
        · -- Sub-case: $a ≥ c$.
          have h_gcd_symm : Nat.gcd a b + Nat.gcd b c + Nat.gcd c a = c.gcd a + a.gcd b + b.gcd c := by
            rw [Nat.gcd_comm a b, Nat.gcd_comm b c]
            linarith
          rw [h_gcd_symm] at h_G
          have h_sum_symm : c + a + b = 5 * n := by
            rw [add_assoc , add_comm , h_sum]
          apply this c a b hc ha hb h_sum_symm h_G
          · linarith
          · linarith
        · -- Sub-case: $a < c$.
          have h_gcd_symm : Nat.gcd a b + Nat.gcd b c + Nat.gcd c a = a.gcd c + c.gcd b + b.gcd a := by
            rw [Nat.gcd_comm c a, Nat.gcd_comm b c, Nat.gcd_comm a b]
            linarith
          rw [h_gcd_symm] at h_G
          have h_sum_symm : a + c + b = 5 * n := by
            rw [add_assoc, add_comm c b, ← add_assoc, h_sum]
          apply this a c b ha hc hb h_sum_symm h_G
          · linarith
          · linarith
      · -- Sub-branch: $a ≤ b ∧ b ≤ c$.
        have h_G_bound : x ≤ 5 * n := by
          simp only [h_G]
          have h_gcd_ab_le : Nat.gcd a b ≤ a := Nat.gcd_le_left b ha
          have h_gcd_bc_le : Nat.gcd b c ≤ b := Nat.gcd_le_left c hb
          have h_gcd_ca_le : Nat.gcd c a ≤ c := Nat.gcd_le_left a hc
          linarith
        -- Step $3$: If $3 ∣ n$, $G = 5n$ is achievable.
        have h_div_3 : 3 ∣ n → x ≤ 5 * n := by
          intro h_3_div_n
          obtain ⟨k, hk⟩ := h_3_div_n
          have h_dvd: 3 ∣ n * 5 := by omega
          have h_abc : ∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 5 * n ∧
              Nat.gcd a b + Nat.gcd b c + Nat.gcd c a = 5 * n := by
            exists 5 * n / 3, 5 * n / 3, 5 * n / 3
            have h_a_pos : 5 * n / 3 > 0 := by
              apply Nat.div_pos
              · linarith
              · norm_num
            have h_sum : 5 * n / 3 + 5 * n / 3 + 5 * n / 3 = 5 * n := by
              ring_nf
              apply Nat.div_mul_cancel
              exact h_dvd
            have h_gcd_eq : Nat.gcd (5 * n / 3) (5 * n / 3) + Nat.gcd (5 * n / 3) (5 * n / 3) + Nat.gcd (5 * n / 3) (5 * n / 3) = 5 * n := by
              rw [Nat.gcd_self]
              ring_nf
              apply Nat.div_mul_cancel
              exact h_dvd
            simp only [h_a_pos, h_sum, h_gcd_eq, true_and]
          obtain ⟨a', b', c', ha', hb', hc', h_sum', h_G_max⟩ := h_abc
          apply le_trans h_G_bound
          linarith
        -- Step $4$: If $3 ∤ n$, analyze cases.
        have h_not_div_3 : ¬(3 ∣ n) → x ≤ 4 * n := by
          intro h_3_not_div
          have h_gcd_ab_le : Nat.gcd a b ≤ a := Nat.gcd_le_left b ha
          have h_gcd_bc_le : Nat.gcd b c ≤ b := Nat.gcd_le_left c hb
          have h_gcd_ca_le : Nat.gcd c a ≤ a := by rw [Nat.gcd_comm];exact Nat.gcd_le_left c ha
          have h_sum_le : a + b + c = 5 * n := by omega
          have h_a_b_c_pos : a > 0 ∧ b > 0 ∧ c > 0 := ⟨ha, hb, hc⟩
          have h_gcd_sum_le : Nat.gcd a b + Nat.gcd b c + Nat.gcd c a ≤ a + b + a := by
            linarith
          have h_gcd_sum_le' : Nat.gcd a b + Nat.gcd b c + Nat.gcd c a ≤ 4 * n := by
            by_cases h_bc_eq : b = c
            -- case $1a$: $b = c$ and $b ≤ 2 n$.
            · by_cases h_b_le_2n : b ≤ 2 * n
              · have h₁: Nat.gcd a b = Nat.gcd a (b - a):= by
                  have : Nat.gcd a b = Nat.gcd a (b - 1 * a) := by
                      apply gcd_sub_multiple a b 1
                      linarith
                  rw [mul_comm, mul_one] at this
                  exact this
                have h₂: Nat.gcd a b ≤ b - a := by
                  have : Nat.gcd a (b - a) ≤ b - a := Nat.gcd_le_right (b - a) (by omega)
                  rw [← h₁] at this
                  exact this
                have h₃: Nat.gcd a b + Nat.gcd b c + Nat.gcd c a ≤ (b - a) + b + a := by nlinarith
                have h₄: Nat.gcd a b + Nat.gcd b c + Nat.gcd c a ≤ 4 * n := by omega
                exact h₄
              -- case $1b$: $b = c$ and $b > 2 n$.
              · nlinarith
            -- case $2a$: $b ≠  c$ and $c - a ≥ n$.
            · by_cases h_csa_le_n : c - a ≥  n
              · have : a + b + a = a + b + c - (c - a) := by omega
                have : a + b + a ≤ 4 * n := by omega
                nlinarith
              -- case $2b$: $b ≠ c$ and $c - a < n$.
              · have h₁: c - a < n := by omega
                have h₂: Nat.gcd c a = Nat.gcd a (c - a) := by
                  have : Nat.gcd a c = Nat.gcd a (c - 1 * a) := by
                      apply gcd_sub_multiple a c 1
                      linarith
                  rw [mul_comm, mul_one, Nat.gcd_comm] at this
                  exact this
                have h₃: Nat.gcd c a ≤ (c - a) := by
                  have : Nat.gcd a (c - a) ≤ c - a := Nat.gcd_le_right (c - a) (by omega)
                  rw [← h₂] at this
                  exact this
                have h_bc: Nat.gcd b c = Nat.gcd b (c - b) := by
                  have : Nat.gcd b c = Nat.gcd b (c - 1 * b) := by
                      apply gcd_sub_multiple b c 1
                      linarith
                  rw [mul_comm, mul_one] at this
                  exact this
                have h₄: Nat.gcd b c ≤ (c - b) := by
                  have : Nat.gcd b (c - b) ≤ c - b := Nat.gcd_le_right (c - b) (by omega)
                  rw [← h_bc] at this
                  exact this
                have h₅: a ≤ 5 * n / 3 := by omega
                have h₆ : Nat.gcd a b + Nat.gcd b c + Nat.gcd c a ≤ 4 * n := by omega
                exact h₆
          have h_gcd_sum_le'' : x ≤ 4 * n := by
            simp_all [h_G]
          exact h_gcd_sum_le''
        -- step $5$: Combine cases.
        have h_max : x ≤ (if 3 ∣ n then 5 * n else 4 * n) := by
          by_cases h_3_div : 3 ∣ n
          · rw [if_pos h_3_div]
            exact h_div_3 h_3_div
          · rw [if_neg h_3_div]
            exact h_not_div_3 h_3_div
        exact h_max