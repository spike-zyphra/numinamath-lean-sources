import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

set_option maxHeartbeats 600000

/- Find all triplets  $(x,y,p)$  of positive integers such that  $p$  be a prime number and
  $\frac{xy^3}{x+y}=p$. -/
theorem number_theory_8937 :
  {(x, y, p) : ℕ × ℕ × ℕ | 0 < x ∧ 0 < y ∧ p.Prime ∧ x * y^3  = p * (x + y)} = {(14, 2, 7)} := by
    -- in this proof, $x.1$ denotes $x$, $x.2.1$ denotes y, $x.2.2$ denotes p.
    ext x; simp; constructor
    · intro ⟨hx, hy, hp, h⟩
      -- $p \ne 0$
      have ppos : x.2.2 ≠ 0 := by have := Nat.Prime.pos hp; linarith
      have h1 : x.2.2 ∣ x.1 * x.2.1^3 := ⟨x.1 + x.2.1, h⟩
      -- $p \mid x or p \mid y$
      have h2 : x.2.2 ∣ x.1 ∨ x.2.2 ∣ x.2.1 := by
        have := (Nat.Prime.dvd_mul hp).1 h1
        rcases this with hl | hr <;> try tauto
        right; exact Nat.Prime.dvd_of_dvd_pow hp hr
      rcases h2 with pdvdx | pdvdy
      · -- case $p \mid x$ : let $x =kp$ and substituting back to find $kp = y(ky^2 - 1)$
        obtain ⟨k, hk⟩ := pdvdx
        simp [hk] at h
        have c1: x.2.1 = k * x.2.1^3 - k * x.2.2 := by
            rw [mul_assoc] at h
            have := Nat.mul_left_cancel (Nat.Prime.pos hp) h
            rw [mul_comm x.2.2 k] at this
            refine Nat.eq_sub_of_add_eq' this.symm
        -- $kp = y (ky^2 -1)$
        have c2 : k * x.2.2 = x.2.1 * (k * x.2.1^2 - 1) := by
          have :  k * x.2.2 = k * x.2.1^3 - x.2.1 :=
            Eq.symm (Nat.sub_eq_of_eq_add (by nlinarith))
          simp [Nat.mul_sub]; ring_nf; exact this
        -- so we can get $p \mid y or p \mid (ky^2-1)$.
        have h2 : x.2.2 ∣ x.2.1 ∨ x.2.2 ∣ k * x.2.1^2 - 1 :=
          (Nat.Prime.dvd_mul hp).1 (show x.2.2 ∣ x.2.1 * (k * x.2.1^2 - 1) by
            exact Dvd.intro_left k c2)
        rcases h2 with  pdvdy | pdvdbulabula
        · -- case $p \mid y$ : there is a contradiction.
          obtain ⟨n, hn⟩ := pdvdy

          nth_rw 1 [hn, mul_comm, mul_assoc] at c2
          have c0: k = n * (k * x.2.1^2 - 1) := Nat.mul_left_cancel (Nat.Prime.pos hp) c2
          have kpos : k ≠ 0 := by
            intro tmp; simp [tmp] at c1; linarith
          have npos : n ≠ 0 := by
            intro tmp; simp [tmp] at c2;
            have := Nat.Prime.pos hp
            have : ¬ (x.2.2 = 0 ∨ k = 0) := by
              push_neg; exact ⟨by positivity, kpos⟩
            exact this c2
          have bulabulapos : (k * x.2.1 ^ 2 - 1) ≠ 0 := by
            intro tmp; simp [tmp] at c2
            have : ¬ (x.2.2 = 0 ∨ k = 0) := by
              push_neg; tauto
            exact this c2
          have c3 : n = k / (k * x.2.1 ^ 2 - 1) :=
            Nat.eq_div_of_mul_eq_left bulabulapos (id (Eq.symm c0))
          have kne1 : k ≠ 1 := by
            intro tmp; simp [tmp] at c0
            have : x.2.1^2 -1 = 1 := by exact eq_one_of_mul_eq_one_left (id (Eq.symm c0))
            have : x.2.1^2 = 2 := by exact pred_eq_succ_iff.mp this
            have : x.2.1 < 2 := by nlinarith
            interval_cases x.2.1 ;tauto
          have c4 : n ≤ k / (k - 1) := by
            have :  k - 1 ≤  k * x.2.1^2 - 1 := by
              simp
              rw [Nat.sub_add_cancel (by nlinarith)]
              nth_rw 1 [←mul_one k]
              refine Nat.mul_le_mul_left k (by nlinarith)
            rw [c3]
            refine Nat.div_le_div_left this ?hc
            omega
          have c5 : k / (k - 1) ≤ 2 := by
            apply Nat.div_le_of_le_mul
            omega
          have : n ≤ 2 := by linarith
          interval_cases n <;> try tauto
          · -- case $n = 1$
            have : x.2.1 < 2 := by
              by_contra! tmp
              have : k * 4 ≤ k * x.2.1^2 := Nat.mul_le_mul_left k (by nlinarith)
              have : 4 * k - 1 ≤ k := by omega
              omega
            interval_cases x.2.1 <;> try tauto
            rw [Nat.one_pow 2, mul_one,one_mul] at c0
            exfalso; have := (Nat.sub_one_eq_self).1 c0.symm; tauto
          · -- case $n = 2$
            have k1 : k / (k - 1) = 2 := Nat.eq_iff_le_and_ge.2 ⟨c5, c4⟩
            have : k = 2 := by
              have := Nat.div_add_mod' k (k-1)
              rw [k1] at this
              cases' k with k
              · norm_num at k1
              cases' k with k
              · norm_num at k1
              omega
            simp [this] at c0
            have : x.2.1 = 1 := by
              have : x.2.1^2 = 1 := by
                have := Nat.eq_add_of_sub_eq (by nlinarith) c0
                simp at this; exact this
              exact eq_one_of_mul_eq_one_left this
            simp [this] at hn
            exfalso; have : 2 ∣ 1 := Dvd.intro_left x.2.2 (id (Eq.symm hn))
            tauto

        · -- case $p \mid ky^2 - 1$, we get $(x,y,p) = (14,2,7)$
          obtain ⟨m, hm⟩ := pdvdbulabula
          rw [hm] at c2
          have c3 : k = x.2.1 * m:= by
            rw [mul_comm x.2.2 m, ←mul_assoc] at c2
            exact Nat.mul_right_cancel (by omega) c2
          have c4 : m * (x.2.1^3 - x.2.2) = 1 := by
            rw [c3, mul_comm x.2.1 m, mul_assoc, mul_comm x.2.2 m] at hm
            nth_rw 1 [←Nat.pow_one x.2.1, ←Nat.pow_add] at hm
            simp at hm
            rw [Nat.mul_sub]
            apply Nat.sub_eq_of_eq_add
            rw [←hm, add_comm, Nat.sub_add_cancel]
            have mpos : m ≠ 0 := by
              intro tmp; simp [tmp] at c3; simp [c3] at c1; linarith
            nlinarith
          have c5 : x.2.1^3 - x.2.2 = 1 := by exact eq_one_of_mul_eq_one_left c4
          replace c5 : x.2.1^3 - 1 = x.2.2 := by
            apply Nat.sub_eq_of_eq_add
            rw [←c5, add_comm, Nat.sub_add_cancel (by nlinarith)]
          have c6 : (x.2.1 - 1) * (x.2.1^2 + x.2.1 + 1) = x.2.1^3 - 1 := by
            zify
            rw [Nat.cast_sub (by linarith), Nat.cast_sub (one_le_pow 3 x.2.1 hy), Nat.cast_pow]
            ring_nf
          rw [c5] at c6
          rcases Nat.prime_mul_iff.1 (c6 ▸ hp) with hl | hr
          · have : x.2.1^2 + x.2.1 = 0 := by linarith
            have : x.2.1 = 0 := by nlinarith
            exfalso
            exact Nat.ne_of_gt hy this
          · have : x.2.1 = 2 := Nat.eq_add_of_sub_eq (by linarith) hr.2
            have m1 : m = 1 := by exact eq_one_of_mul_eq_one_right c4
            simp [this] at c6
            simp [this, m1] at c3
            simp [c3, ←c6] at hk
            ext <;> simp [c6, this, hk]
      -- case $p \mid y$, let $y = rp$ and substituting into the equation
      -- $x * y ^ 3 = p * (x + y)$.
      · obtain ⟨r, hr⟩ := pdvdy
        have rpos : r ≠ 0 := by intro tmp; simp [tmp] at hr; linarith
        have c1: x.1 = (x.1 * r^3 * x.2.2 - r) * x.2.2 := by
          simp [hr] at h
          simp [Nat.sub_mul]
          ring_nf at h
          apply Nat.eq_sub_of_add_eq
          apply Nat.mul_right_cancel (show 0 < x.2.2 from Nat.Prime.pos hp)
          nlinarith
        -- $p \mid x$
        have pdvdx : x.2.2 ∣ x.1 :=
          Dvd.intro_left (x.1 * r ^ 3 * x.2.2 - r) (id (Eq.symm c1))
        obtain ⟨t, ht⟩ := pdvdx
        have tpos : t ≠ 0 := by intro tmp; simp [tmp] at ht; linarith
        -- $r \mid t$.
        have rdvdt : r ∣ t := by
          nth_rw 1 [ht, mul_comm] at c1
          have := Nat.mul_right_cancel (by omega) c1
          have : t = (x.1 * r^2 * x.2.2 - 1) * r := by rw [this, Nat.sub_mul]; ring_nf
          exact Dvd.intro_left (x.1 * r ^ 2 * x.2.2 - 1) (id (Eq.symm this))
        simp [ht] at c1
        rw [mul_comm x.2.2 t] at c1
        have c2 := Nat.mul_right_cancel (by omega) c1

        have : r = t * (x.2.2 * r^3 * x.2.2 - 1) := by
            rw [Nat.mul_sub]
            ring_nf
            apply Nat.eq_sub_of_add_eq
            nth_rw 1 [c2, add_comm, Nat.sub_add_cancel]
            nlinarith
            exact (show r ≤ r^3 by refine Nat.le_self_pow (by simp) r).trans (by
                ring_nf; nth_rw 1 [mul_assoc, ←mul_one (r^3)]
                refine Nat.mul_le_mul_left (r ^ 3) ?h
                nlinarith)
        -- $t \mid r$
        have tdvdr : t ∣ r := Dvd.intro (x.2.2 * r ^ 3 * x.2.2 - 1) (id (Eq.symm this))
        -- because $r \mid t$ and $t \mid r$, so $r = t$.
        have reqt : r = t := Nat.dvd_antisymm rdvdt tdvdr
        -- substituting $r$ with $t$ and simplifying we can get $p^2 * t^3 = 2$ which is impossible.
        -- so the only solution is $x = (14, 2, 7)$.
        rw [reqt] at c2
        have c3 : x.2.2^2 * t^3 = 2 := by
          have : 1 = x.2.2 * t^3 * x.2.2 - 1 := by
            nth_rw 4 [←mul_one t] at c2
            rw [mul_assoc, mul_assoc, ←Nat.mul_sub] at c2
            nth_rw 1 [←mul_one t, ←mul_assoc] at c2
            exact Nat.mul_left_cancel (by omega) c2
          rw [mul_assoc, mul_comm (t^3) x.2.2, ←mul_assoc, ←pow_two] at this
          exact Nat.eq_add_of_sub_eq (by refine one_le_iff_ne_zero.mpr (by
            refine Nat.mul_ne_zero (pow_ne_zero 2 ppos) (pow_ne_zero 3 tpos))) this.symm
        have : t < 2 := by
          have :  t^3 ≤ 2 := by
            calc
              _ ≤ x.2.2 ^ 2 * t ^ 3 := Nat.le_mul_of_pos_left (t ^ 3) (pow_two_pos_of_ne_zero ppos)
              _ = _ := c3
          by_contra! tmp
          have : 2^3 ≤ t^3 := by exact Nat.pow_le_pow_of_le_left tmp 3
          nlinarith
        have t1 : t = 1 := by omega
        simp [t1, pow_two] at c3
        have : x.2.2 ∣ 2 := by exact Dvd.intro x.2.2 c3
        have : x.2.2 = 1 ∨  x.2.2 = 2 := (dvd_prime Nat.prime_two).mp this
        rcases this with pp | pp <;> simp [pp] at c3
    · intro h
      simp [h]
      decide
