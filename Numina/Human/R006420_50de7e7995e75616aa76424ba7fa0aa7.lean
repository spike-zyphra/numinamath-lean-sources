import Mathlib
open Nat

/-!
We define a sequence \( a : \mathbb{N} \to \mathbb{N} \) recursively by:
- a(1) = 1
- For n > 1, a(n) = gcd(n, a(n-1)) + 1)
-/
theorem a_p_plus_three_eq_three_of_prime_7_mod12
  (a : (n : ℕ) → ℕ)
  (ha_1 : a 1 = 1)
  (ha_n :∀ n > 1, a n = (n.gcd (a (n - 1))) + 1 )
  (hp:Nat.Prime p ∧ p ≥ 7 ∧ ∃ k,p = 12 * k + 7):
  a (p + 3) = 3 :=
by
  -- Case split on gcd(p, a(p-1)) = 1 or p (since p is prime)
  let r:=ha_n p (by omega)  -- a(p) = gcd(p, a(p-1)) + 1
  obtain⟨hp1,hp2,k,hk⟩:=hp  -- Extract prime facts and p=12k+7
  have r1:p.gcd (a (p - 1)) ∣ p:=by exact Nat.gcd_dvd_left p (a (p - 1))  -- gcd divides p
  have r2:p.gcd (a (p - 1)) = 1 ∨ p.gcd (a (p - 1)) = p:=by refine (dvd_prime hp1).mp r1  -- Prime divisor cases
  cases r2
  case inl H=>  -- Case 1: gcd(p, a(p-1)) = 1
    simp[H] at r  -- Thus a(p) = 1 + 1 = 2
    let r':=ha_n (p+1) (by omega)  -- a(p+1) = gcd(p+1, a(p)) + 1
    simp[r] at r'  -- Substitute a(p)=2 → a(p+1)=gcd(p+1,2)+1
    -- Prove gcd(p+1,2)=2 (since p≡7 mod 12 → p+1 even and not divisible by 4)
    have t1: (p + 1).gcd 2 = 2:=by
      refine gcd_eq_right ?_
      simp[hk]  -- p+1 = 12k+8 = 4(3k+2)
      refine (Nat.Prime.dvd_mul ?_).mpr ?_  -- Show 2 ∣ 12k+8
      trivial  -- 2 is prime
      left  -- 2 divides 12 (since 12=2*6)
      trivial  -- 2∣12
    simp[t1] at r'  -- Thus a(p+1)=2+1=3
    let r'':=ha_n (p+2) (by omega)  -- a(p+2)=gcd(p+2, a(p+1)) + 1
    simp[r'] at r''  -- Substitute a(p+1)=3 → a(p+2)=gcd(p+2,3)+1
    -- Prove gcd(p+2,3)=3 (since p≡7 mod 12 → p+2=12k+9 divisible by 3)
    have t2:(p + 2).gcd 3 = 3:=by
      refine gcd_eq_right ?_
      simp[hk]  -- p+2=12k+9
      refine (Nat.Prime.dvd_mul ?_).mpr ?_  -- Show 3 ∣ 12k+9
      trivial  -- 3 is prime
      left  -- 3 divides 12 (12=3*4)
      trivial  -- 3∣12
    simp[t2] at r''  -- Thus a(p+2)=3+1=4
    let r''':=ha_n (p+3) (by omega)  -- a(p+3)=gcd(p+3, a(p+2)) + 1
    simp[r''] at r'''  -- Substitute a(p+2)=4 → a(p+3)=gcd(p+3,4)+1
    -- Prove gcd(p+3,4)=2 (since p≡7 mod 12 → p+3=12k+10 ≡ 10 mod 12, gcd(10,4)=2)
    have t3:(p + 3).gcd 4 = 2:=by
      refine Eq.symm (Nat.gcd_greatest ?_ ?_ ?_)  -- Greatest common divisor is 2
      simp[hk]  -- p+3=12k+10
      refine (Nat.Prime.dvd_mul ?_).mpr ?_  -- Show 2 ∣ 12k+10
      trivial  -- 2 is prime
      left  -- 2 divides 12
      trivial  -- 2∣12
      trivial  -- 2∣4 (trivial)
      intro e he1 he2  -- Show any common divisor e of 12k+10 and 4 must divide 2
      have he:e ≤ 4 :=by  -- e|4 → e≤4
        refine (le_iff_ne_zero_of_dvd ?_ he2).mpr ?_
        by_contra w
        simp[w] at he2  -- e≠0
        trivial
      have he':e=0∨ e=1∨e=2∨e=3∨e=4:=by omega  -- Exhaust possible e≤4
      rcases he' with h11 | h11 | h11 | h11 | h11  -- Check each case
      all_goals simp[h11] at he2  -- e=0 impossible (already handled)
      all_goals simp[h11]  -- e=1,2,3,4
      by_contra w  -- For e=1: no contradiction needed
      revert he2  -- For e=3: must show 3∤12k+10
      simp  -- Clear context
      exact of_decide_eq_false rfl  -- Decide ¬(3∣10) since 10%3=1
      simp[h11,hk] at he1  -- e=4: 4∣12k+10 → 4∣10 (since 4∣12k) → contradiction
      have p1:4 ∣ 12*k :=by
        rw[mul_comm]  -- 12k = k*12
        refine Dvd.dvd.mul_left ?_ k  -- 4∣12 (since 12=4*3)
        trivial
      have p2:4∣2:=by exact (Nat.dvd_add_iff_right p1).mpr he1  -- 4∣(12k+10 - 12k)=10 → 4∣2, absurd
      tauto
    simp[t3] at r'''  -- Thus a(p+3)=2+1=3
    tauto  -- Goal: a(p+3)=3

  case inr H =>  -- Case 2: gcd(p, a(p-1)) = p
    simp[H] at r  -- Thus a(p)=p+1
    have ha_npos:1≤a (p - 1):=by
      rw [ha_n (p - 1)]
      simp -- get p - 1 > 1
      omega
    -- Since gcd=p, p divides a(p-1)
    have H_dvd : p ∣ a (p - 1) := by
      exact gcd_eq_left_iff_dvd.mpr H

    -- Bound: a(p-1) ≤ p
    have a_bound : a (p - 1) ≤ p := by
      rw [ha_n (p - 1)]  -- a(p-1)=gcd(p-1, a(p-2))+1
      have t1:(p - 1).gcd (a (p - 1 - 1)) ≤ p - 1:=by
        have m1:1≤p-1:=by omega
        have m2:1≤a (p - 1-1):=by
          rw [ha_n (p - 1-1)]  -- Prove positivity via recurrence
          simp -- get p - 1 > 1
          omega
        exact gcd_le_left (a (p - 1 - 1)) m1  -- gcd(_,b) ≤ _
      refine add_le_of_le_sub ?hle t1  -- (gcd ≤ p-1) → (gcd+1 ≤ p)
      omega  -- p-1 +1 = p, and 1≤gcd+1
      omega  -- p-1>1 since p≥7

    -- Combine: p | a(p-1) and a(p-1)≤p → a(p-1)=p
    have a_p1 : a (p - 1) = p :=by
      refine Nat.le_antisymm a_bound ?h₂
      have helper:a (p - 1)≠0:=by exact not_eq_zero_of_lt ha_npos  -- a(p-1)≥1
      exact le_of_dvd (by omega) H_dvd  -- p ≤ a(p-1) since p|a(p-1) and a(p-1)>0

    -- Key lemma: ∀i ∈ [2, p-1], a(i)=i+1 (proved by downward induction from p-1)
    have rec : ∀ i, 2 ≤ i → i ≤ p - 1 → a i = i + 1 := by
      have rec_aux : ∀ m, m ≤ p - 3 → a (p - 1 - m) = (p - 1 - m) + 1 := by
        intro m hm
        induction m with
        | zero =>  -- Base: m=0 → i=p-1
          rw [Nat.sub_zero, a_p1, add_comm]
          omega  -- p = (p-1)+1
        | succ m' ih =>  -- Inductive step: m = m'+1
          let j := p - 1 - m'.succ  -- Current index
          have hj_eq : j = p - 1 - (m' + 1) := rfl

          -- j+1 = p-1-m'
          have j1_eq : j + 1 = p - 1 - m' := by
            rw [hj_eq, Nat.sub_succ, Nat.add_comm, ← Nat.sub_add_eq]
            refine Eq.symm ((fun {b a c} h => (Nat.sub_eq_iff_eq_add' h).mp) ?h rfl)
            omega  -- p-1-m' ≥ 1 (since m'≤m≤p-3)

          -- Induction hypothesis for j+1 (which is p-1-m')
          have IH_j1 : a (j + 1) = (j + 1) + 1 := by
            rw [j1_eq]
            apply ih
            exact Nat.le_of_succ_le hm  -- m' ≤ m'.succ ≤ p-3 → m'≤p-3

          -- Prove j>1 to use recurrence
          have j_gt1 : j > 1 := by
            rw [hj_eq]
            have : m'.succ ≤ p - 3 := hm
            omega  -- j = p-1 - (m'+1) ≥ 2 (since m'+1≤p-3)

          -- Express a(j+1) via recurrence
          rw [ha_n (j + 1) (by linarith)] at IH_j1  -- a(j+1)=gcd(j+1, a(j))+1
          simp only [add_left_inj] at IH_j1  -- → gcd(j+1, a(j)) = j+1

          -- Thus j+1 | a(j)
          have div_j : j + 1 ∣ a j := by
            have helper:j+1≠0:=by omega
            exact gcd_eq_left_iff_dvd.mpr IH_j1  -- gcd= j+1 → j+1 | a(j)

          -- Bound a(j) ≤ j+1
          have a_j_le : a j ≤ j + 1 := by
            rw [ha_n j j_gt1]  -- a(j)=gcd(j, a(j-1))+1
            apply add_le_add_right
            apply gcd_le_left
            omega  -- j>1 → j≥2>0

          -- Combine: a(j) = j+1 (since j+1 | a(j) and a(j)≤j+1)
          have pos_j : 0 < a j := by
            rw [ha_n j j_gt1]
            apply add_pos
            · apply gcd_pos_of_pos_left; linarith  -- gcd>0
            · exact zero_lt_one
          apply le_antisymm a_j_le
          exact le_of_dvd pos_j div_j  -- a(j) ≥ j+1

      -- Translate auxiliary lemma to desired form
      intro i hi_le2 hi_lep1
      let m := p - 1 - i
      have heq: i = p - 1 - m := by
        rw [Nat.sub_sub, Nat.add_comm]
        omega
      rw [heq]
      apply rec_aux
      rw [heq] at hi_le2
      omega  -- m = p-1-i ≤ p-3 since i≥2

    -- Instantiate lemma at i=2: a(2)=3
    have a2_eq3 : a 2 = 3 :=
      rec 2 (by linarith) (by omega)  -- 2≤2≤p-1 (p≥7)

    -- But direct computation: a(2)=gcd(2,a(1))+1=gcd(2,1)+1=2
    have a2_eq2 : a 2 = 2 := by
      rw [ha_n 2 (by linarith), ha_1,  add_comm, ← Nat.add_succ_sub_one]
      simp  -- gcd(2,1)=1 → 1+1=2

    -- Contradiction: 2=3
    have : 2 = 3 := by rw [← a2_eq2, a2_eq3]
    contradiction
