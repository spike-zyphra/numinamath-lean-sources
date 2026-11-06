import Mathlib


/-Determine all prime numbers $p$ and all positive integers  $x$  and  $y$  satisfying   $$ x^3+y^3=p(xy+p). $$-/
theorem number_theory_8613_1 (x y p : ℤ) (hx : 1 ≤ x) (hy : 1 ≤ y)(hp1 : 1 ≤ p)
(hp : Prime p) (h0 : x ^ 3 + y ^ 3 = p * (x * y + p)) : x + y = 9 := by
-- Prove that $p$ can't divide either $x$ or $y$
  have pdvd0 : ¬ p ∣ x ∧ ¬ p ∣ y := by
    by_contra h'; push_neg at h'; by_cases h'' : p ∣ x
    · rcases h'' with ⟨k, hk⟩; symm at h0; rw [← sub_eq_iff_eq_add', hk] at h0
      have pdy : p ∣ y := by
        rw [← Prime.dvd_pow_iff_dvd hp (show 3≠0 by simp), ← h0]
        use p*k*y+p-p^2*k^3; ring
      rcases pdy with ⟨l, hl⟩; rw [hl, sub_eq_iff_eq_add] at h0
      rw [show p*(p*k*(p*l)+p)=p^2*(p*k*l+1) by ring] at h0
      rw [show (p*l)^3+(p*k)^3=p^2*(p*(l^3+k^3)) by ring] at h0
      simp at h0; cases h0
      · have pd' : p ∣ p * k * l + 1 := by use l ^ 3 + k ^ 3
        rw [dvd_add_right (show p∣p*k*l by use k*l;ring)] at pd'
        rw [← isUnit_iff_dvd_one] at pd'; rw [Prime.eq_1] at hp
        rcases hp with ⟨_,_,_⟩; contradiction
      rename_i h'p; simp [h'p] at hp
    replace h' := h' h''; rcases h' with ⟨m, hm⟩
    symm at h0; rw [← sub_eq_iff_eq_add, hm] at h0
    have : p ∣ x := by
      rw [← Prime.dvd_pow_iff_dvd hp (show 3≠0 by simp), ← h0]
      use p*m*x+p-p^2*m^3; ring
    contradiction

-- Use AM-GM inequality to get the following inequality
  have amgm := two_mul_le_add_sq x y
  have h'0 := h0
-- Factorize the LHS of the equation
  rw [show p=p^1 by simp, mul_comm, show x^3+y^3=(x+y)*(x^2-x*y+y^2) by ring] at h0
-- Apply the key lemma mul_eq_mul_prime_pow to get more information about the factors
  apply mul_eq_mul_prime_pow at h0; rcases h0 with ⟨i, j, u, v, hij, h1, h2, h3⟩
-- In particular, $i$ has to be less or equal to $1$, we discuss by the cases when $i$ equals $1$ or $i$ equals $0$
  have hi : i ≤ 1 := by linarith
  rcases hi with _ | h'
-- Case $i$ equals $1$
  · simp at *; rw [hij] at h3; simp at h3
    have hu1 : 1 ≤ u := by
      by_contra h'; simp at h'; rw [Int.lt_iff_add_one_le] at h'; simp at h'
      rw [Int.le_iff_eq_or_lt] at h'; rcases h' with h'l | h'r
      · rw [h'l] at h2; simp at h2; linarith
      have : x + y < 0 := by
        rw [h2, mul_comm]; apply Int.mul_neg_of_pos_of_neg; linarith; assumption
      linarith
    have hv1 : x * y ≤ v := by
      rw [← Int.sub_nonneg, ← h3, show x^2-x*y+y^2-x*y=(x-y)^2 by ring]; linarith
    have r1 : u * (u - 1) * x * y ≤ x + y := by
      rw [h2, mul_assoc, mul_assoc, mul_comm]; nth_rw 4 [mul_comm]
      rw [Int.mul_le_mul_iff_of_pos_right, sub_mul]; simp
      rw [add_comm, h1, mul_comm]; nth_rw 3 [mul_comm]
      rw [Int.mul_le_mul_iff_of_pos_right]; assumption
      linarith; linarith
    by_cases h'u : 2 < u
    · rcases le_or_gt x y with h' | h'
      · have : u * (u - 1) * x * y ≤ 2 * y := by
          have : x + y ≤ y + y := by linarith
          rw [← two_mul] at this; linarith
        rw [Int.mul_le_mul_iff_of_pos_right] at this
        have : 2 < u * (u - 1) * x := by
          rw [show (2:ℤ)=2*1*1 by norm_num]; apply Int.mul_lt_mul
          apply Int.mul_lt_mul; assumption; linarith; norm_num; linarith
          assumption; norm_num; apply Int.mul_nonneg; linarith; linarith
        linarith; linarith
      rw [gt_iff_lt] at h'
      have : u * (u - 1) * x * y < 2 * x := by
        have : x + y < x + x := by linarith
        rw [← two_mul] at this; linarith
      rw [mul_assoc] at this; nth_rw 3 [mul_comm] at this
      rw [← mul_assoc, mul_lt_mul_iff_of_pos_right] at this
      have : 2 < u * (u - 1) * y := by
        rw [show (2:ℤ)=2*1*1 by norm_num]; apply Int.mul_lt_mul
        apply Int.mul_lt_mul; assumption; linarith; norm_num; linarith
        assumption; norm_num; apply Int.mul_nonneg; linarith; linarith
      linarith; linarith
    simp at h'u; rw [Int.le_iff_eq_or_lt] at h'u
    rcases h'u with h' | h'
    · simp [h'] at h2 r1 h1; rcases le_or_gt x y with h'' | h''
      · have : 2 * x * y ≤ 2 * y := by
          have : x + y ≤ y + y := by linarith
          rw [← two_mul] at this; linarith
        rw [Int.mul_le_mul_iff_of_pos_right] at this; simp at this
        replace hx : x = 1 := by linarith
        simp [hx] at h1 h2 h3; symm at h1; rw [← sub_eq_iff_eq_add'] at h1
        rw [← h1, ← h3] at h2; ring_nf at h2; by_cases h'y : 2 ≤ y
        · have : 4 + y * 2 ≤ 4 - y * 6 + y ^ 2 * 4 := by
            rw [sub_add_comm, add_comm]; simp; rw [le_sub_iff_add_le]
            ring_nf; rw [show (8:ℤ)=2*4 by simp, ← mul_assoc]; simp
            rw [pow_two]; apply mul_le_mul; rfl; assumption; norm_num
            linarith
          rw [← h2] at this; linarith
        simp at h'y
        replace hy : y = 1 := by linarith
        simp [hy] at h3 h1; simp [← h3] at h1; simp [← h1] at hp; linarith
      rw [gt_iff_lt] at h''
      have : 2 * x * y < 2 * x := by
        have : x + y < x + x := by linarith
        rw [← two_mul] at this; linarith
      nth_rw 2 [show 2*x=2*x*1 by simp] at this; rw [mul_lt_mul_iff_of_pos_left] at this
      linarith; linarith
    replace hu1 : u = 1 := by linarith
    simp [hu1] at h2 h1; symm at h1
    rw [← sub_eq_iff_eq_add', ← h3, show x^2-x*y+y^2-x*y=(x-y)^2 by ring] at h1
    simp [← h1] at hp
-- Case $i$ equals $0$
  simp at h' h1; simp [h'] at hij h2; simp [hij] at h3
  have hu : 2 ≤ u := by rw [← h2]; linarith
  have hv : 1 ≤ v := by
    by_contra h'v; simp at h'v; rw [Int.lt_iff_add_one_le] at h'v
    simp at h'v
    have : u * v ≤ 0 := by
      apply Int.mul_nonpos_of_nonneg_of_nonpos; linarith; assumption
    rw [← h1] at this
    have : 0 ≤ x * y := by apply mul_nonneg; linarith; linarith
    linarith
  have h4 : u * (u - 3 * v) = (v - 3) * p ^ 1 := by
    simp; rw [← sub_eq_zero]; ring_nf; rw [← h1, ← h2, ← h3]; ring
-- Apply mul_eq_mul_prime_pow again to get further information about the factors
  apply mul_eq_mul_prime_pow at h4
  rcases h4 with ⟨l, k, s, t, hlk, h5, h6, h7⟩
  have hl1 : l ≤ 1 := by linarith
  cases hl1 with
-- Case $l$ equal $1$, we will prove that $p$ divides $x*y$, which is a contradiction
  | refl =>
    simp at hlk h6; simp [hlk] at h7; symm at h1; rw [h6, ← sub_eq_iff_eq_add] at h1
    have pdvd1 : p ∣ x * y := by use s*v-1; rw [← h1]; ring
    apply Prime.dvd_or_dvd at pdvd1; rcases pdvd1 with _ | _
    · have := pdvd0.left
      contradiction
    have := pdvd0.right; contradiction; assumption
-- Case $l$ equal $0$, we will prove that $v$ equals $3$ via division relations, and this will force $u=x+y$ to be $9$
  | step h =>
    simp at h; simp [h] at h6 hlk; simp [hlk] at h7; rw [← h6] at h5
    by_cases hv : 3 < v
    · have udvd : u ∣ v - 3 := by use t
      apply Int.le_of_dvd at udvd
      have q1 : u * v ≤ x * y + v * p := by
        rw [← h1]; simp
        have : p < 3 * p := by linarith
        have : 3 * p < v * p := by apply mul_lt_mul; assumption; rfl; linarith; linarith
        linarith
      rw [← h3] at q1; ring_nf at q1
      have q2 : x ^ 2 + y ^ 2 ≤ u * u := by
        rw [← h2]; ring_nf; simp; apply mul_nonneg; linarith; linarith
      have : u * v ≤ u * u := by linarith
      rw [mul_le_mul_left] at this; linarith
      rw [← h2]; linarith; linarith
    simp at hv; rw [Int.le_iff_lt_or_eq] at hv; rcases hv with h'v | h'v
    · rw [Int.lt_iff_add_one_le, Int.add_le_iff_le_sub] at h'v; simp at h'v
      rw [Int.le_iff_eq_or_lt] at h'v; rcases h'v with h'vl | h'vr
      · simp [h'vl] at h5 h7 h3; symm at h5; rw [Int.mul_eq_neg_one_iff_eq_one_or_neg_one] at h5
        rcases h5 with ⟨h5l1, h5l2⟩ | ⟨h5r1, h5r2⟩
        · simp [h5l1, h5l2] at h7 h2; simp [← h7, h'vl, h5l1] at h1
          symm at h1; rw [← sub_eq_iff_eq_add] at h1; linarith
        simp [h5r1, h5r2] at h7 h2; linarith
      replace hv : v = 1 := by linarith
      simp [hv] at h7 h5 h3 h1
      have hu1 : u = 2 := by
        have : u ∣ 2 := by use -t; simp; rw [← h5]; simp
        apply Int.le_of_dvd at this; linarith; norm_num
      simp [hu1] at h5 h7
      have : IsUnit p := by
        rw [isUnit_iff_dvd_one]; use -t; simp; rw [mul_comm, ← h7]; simp
      rw [Prime.eq_1] at hp; rcases hp with ⟨_,_,_⟩; contradiction
    simp [h'v] at h5; rcases h5 with h5l | h5r
    · linarith
    simp [h5r, h'v] at h7; rw [sub_eq_zero, ← h2] at h7; assumption
  assumption; assumption
-- Therefore we only need to check when $x$ equals $1,2,3...8$ and find out that the only solutions
-- are $(x,y,p)$ equals $(8,1,19), (1,8,19), (7,2,13), (2,7,13), (5,4,7), (4,5,7)$

/-Determine all prime numbers $p$ and all positive integers  $x$  and  $y$  satisfying   $$ x^3+y^3=p(xy+p). $$-/
theorem number_theory_8613_2 : ∀ x y p : ℤ, 1 ≤ x ∧ 1 ≤ y ∧ 1 ≤ p ∧
Prime p ∧ x ^ 3 + y ^ 3 = p * (x * y + p) ↔ (x = 8 ∧ y = 1 ∧ p = 19) ∨
(x = 1 ∧ y = 8 ∧ p = 19) ∨ (x = 7 ∧ y = 2 ∧ p = 13) ∨
(x = 2 ∧ y = 7 ∧ p = 13) ∨ (x = 5 ∧ y = 4 ∧ p = 7) ∨ (x = 4 ∧ y = 5 ∧ p = 7) := by
-- Apply number_theory_8613_1 and check every cases
  intro x y p; constructor
  · rintro ⟨hx, hy, hp1, hp, h0⟩
    have xay := number_theory_8613_1 x y p hx hy hp1 hp h0
-- Prove that $x$ is less or equal to $8$
    have : x ≤ 8 := by linarith
-- Use "interval_cases" to split the goal to $8$ cases
-- and solve for $y$ in all the cases using "all_goals" command
    interval_cases x
    all_goals symm at xay; rw [← sub_eq_iff_eq_add'] at xay; norm_num at xay
    all_goals symm at xay; simp_all
-- In the first case, prove that $p$ is $19$ by solving the equation
    · rw [← sub_eq_zero] at h0
      rw [show (513:ℤ)-p*(8+p)=(19-p)*(27+p) by ring] at h0
      simp at h0; cases h0; linarith; linarith
-- In the second case, prove that $p$ is $13$ by solving the equation
    · rw [← sub_eq_zero] at h0
      rw [show (351:ℤ)-p*(14+p)=(13-p)*(27+p) by ring] at h0
      simp at h0; cases h0; linarith; linarith
-- In the third case, prove that $p$ has to be $3$ but this
-- does not satisfy the equation
    · have : p ∣ 3 ^ 5 := by use (18+p); norm_num; assumption
      apply Prime.dvd_of_dvd_pow at this
      rw [Prime.dvd_prime_iff_associated, Int.associated_iff] at this
      cases this; simp_all; simp_all
      assumption; exact Int.prime_three; assumption
-- In the 4th case, prove that $p$ is $7$ by solving the equation
    · rw [← sub_eq_zero] at h0
      rw [show (189:ℤ)-p*(20+p)=(7-p)*(27+p) by ring] at h0
      simp at h0; cases h0; linarith; linarith
-- In the 5th case, prove that $p$ is $7$ by solving the equation
    · rw [← sub_eq_zero] at h0
      rw [show (189:ℤ)-p*(20+p)=(7-p)*(27+p) by ring] at h0
      simp at h0; cases h0; linarith; linarith
-- In the 6th case, prove that $p$ has to be $3$ but this
-- does not satisfy the equation
    · have : p ∣ 3 ^ 5 := by use (18+p); norm_num; assumption
      apply Prime.dvd_of_dvd_pow at this
      rw [Prime.dvd_prime_iff_associated, Int.associated_iff] at this
      cases this; simp_all; simp_all
      assumption; exact Int.prime_three; assumption
-- In the 7th case, prove that $p$ is $13$ by solving the equation
    · rw [← sub_eq_zero] at h0
      rw [show (351:ℤ)-p*(14+p)=(13-p)*(27+p) by ring] at h0
      simp at h0; cases h0; linarith; linarith
-- In the last case, prove that $p$ is $19$ by solving the equation
    · rw [← sub_eq_zero] at h0
      rw [show (513:ℤ)-p*(8+p)=(19-p)*(27+p) by ring] at h0
      simp at h0; cases h0; linarith; linarith
-- Conversely, check that all the solutions satisfy the assumptions
  intro h; rcases h with h|h|h|h|h|h
  all_goals simp_all; decide
