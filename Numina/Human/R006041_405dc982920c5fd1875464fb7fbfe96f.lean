import Mathlib

open Finset Real Nat

/-Find all positive integer solutions (m,n) to the following equation:
 m ^ 2= 1!+2!+⋯+n!.-/
theorem number_theory_611255: {(m,n): ℕ × ℕ | (m ^ 2 = ∑ i ∈ Icc 1 n, Nat.factorial i) ∧ (1 ≤ m) ∧ (1 ≤ n)} = {(1,1), (3,3)} := by
  have sq_mod10: ∀ x: ℤ, ¬ 10 ∣ x ^ 2 - 3 := by
    intro x h
  -- Show that x^2 mod 10 must be 3 for 10 to divide x^2 - 3
    let a:= x % 10
    have ha: x % 10 = a := by
      simp [a]
    have a2: a ≤ 9 := by
      simp [a]
      omega
    have aa: a ∈ Icc 0 9 := by
      simp
      omega
    let b:= x/10
    have hx: x = 10 * b + a := by
      simp [a,b]
      omega
    rw [hx] at h
    rw [show (10 * b + a) ^ 2 - 3 = 10 * ((10 * b * b) + 2 * b * a) + (a ^ 2 - 3) by ring_nf] at h
    have o: 10 ∣ 10 * (10 * b * b + 2 * b * a) := by
      omega
    have q: 10 ∣ a ^ 2 - 3 := by omega
    clear * - aa q
    clear_value a
    fin_cases aa
    all_goals simp at q; omega
  -- one can prove this by directly check --
  have id2: ∑ i ∈ Icc 1 2, i ! = 3 := by
    rw [Finset.sum_Icc_succ_top]
    simp
    omega
  have id3: ∑ i ∈ Icc 1 3, i ! = 9 := by
    rw [Finset.sum_Icc_succ_top]
    rw [id2]
    simp [factorial]
    omega
  -- key lemma for proof --
  have mod10: ∀ t: ℕ, 4 ≤ t →  10 ∣ (∑ i ∈ Icc 1 t, i !) - 3 := by
      intro t
      induction' t with n hn
      . omega
      . by_cases o: n ≤ 2
        . all_goals omega
        . by_cases e: n = 3
          . rw [e]
            simp
            rw [Finset.sum_Icc_succ_top]
            rw [id3]
            simp [factorial]
            omega
            omega
          . replace e: 4 ≤ n := by omega
            simp [e]
            intro ee
            clear ee o
            simp [e] at hn
            rw [Finset.sum_Icc_succ_top]
            have iccU: Icc 1 2 ∪ Icc 3 n = Icc 1 n := by
              ext a
              rw [Finset.mem_union]
              simp [Finset.mem_Icc]
              omega
            have h_disjoint : Disjoint (Finset.Icc 1 2) (Finset.Icc 3 n) := by
               apply Finset.disjoint_left.mpr
               intro x hx1 hx2
               have hx1' := Finset.mem_Icc.mp hx1
               have hx2' := Finset.mem_Icc.mp hx2
               linarith
            have ineq: 3 ≤ ∑ i ∈ Icc 1 n, i ! := by
              calc
                3 = ∑ i ∈ Icc 1 2, i ! := by rw [id2]
                _ ≤ (∑ i ∈ Icc 1 2, i !) + (∑ i ∈ Icc 3 n, i !) := by simp
                _ = ∑ i ∈ Icc 1 n, i ! := by rw [← Finset.sum_union h_disjoint]; rw [iccU];
            have dvdf: 10 ∣(n + 1) ! := by
              have p: 5 ! ∣ (n + 1) ! := by
                apply Nat.factorial_dvd_factorial
                omega
              have q: 10 ∣5 ! := by
                simp [factorial]
                omega
              apply Nat.dvd_trans q p
            have v: (∑ k ∈ Icc 1 n, k !) + (n + 1)! - 3 = (∑ k ∈ Icc 1 n, k !) - 3 + (n + 1) ! := by
              apply Nat.sub_add_comm
              exact ineq
            rw [v]
            omega
            omega
  ext x
  constructor
  . simp
    intro h
    intro h2
    intro h3
    have b: x.2 ≤ 3 := by
      by_contra! b
      by_cases s: x.1 < 2
      . have q: x.1 = 1 := by omega
        simp [q] at *
        have iccU: Icc 1 2 ∪ Icc 3 x.2 = Icc 1 x.2 := by
              ext a
              rw [Finset.mem_union]
              simp [Finset.mem_Icc]
              omega
        have h_disjoint : Disjoint (Finset.Icc 1 2) (Finset.Icc 3 x.2) := by
               apply Finset.disjoint_left.mpr
               intro x hx1 hx2
               have hx1' := Finset.mem_Icc.mp hx1
               have hx2' := Finset.mem_Icc.mp hx2
               linarith
        have ineq: 3 ≤ ∑ i ∈ Icc 1 x.2, i ! := by
              calc
                3 = ∑ i ∈ Icc 1 2, i ! := by rw [id2]
                _ ≤ (∑ i ∈ Icc 1 2, i !) + (∑ i ∈ Icc 3 x.2, i !) := by simp
                _ = ∑ i ∈ Icc 1 x.2, i ! := by rw [← Finset.sum_union h_disjoint]; rw [iccU];
        omega
      . replace h: x.1 ^ 2 - 3 = (∑ i ∈ Icc 1 x.2, i !) - 3 := by omega
        specialize mod10 x.2
        replace b: 4 ≤ x.2 := by omega
        simp [b] at mod10
        rw [← h] at mod10
        specialize sq_mod10 x.1
        have iccU: Icc 1 2 ∪ Icc 3 x.2 = Icc 1 x.2 := by
                ext a
                rw [Finset.mem_union]
                simp [Finset.mem_Icc]
                omega
        have h_disjoint : Disjoint (Finset.Icc 1 2) (Finset.Icc 3 x.2) := by
                apply Finset.disjoint_left.mpr
                intro x hx1 hx2
                have hx1' := Finset.mem_Icc.mp hx1
                have hx2' := Finset.mem_Icc.mp hx2
                linarith
        have ineq: 3 ≤ ∑ i ∈ Icc 1 x.2, i ! := by
                calc
                  3 = ∑ i ∈ Icc 1 2, i ! := by rw [id2]
                  _ ≤ (∑ i ∈ Icc 1 2, i !) + (∑ i ∈ Icc 3 x.2, i !) := by simp
                  _ = ∑ i ∈ Icc 1 x.2, i ! := by rw [← Finset.sum_union h_disjoint]; rw [iccU];


        simp at s
        clear * - s sq_mod10 mod10
        absurd sq_mod10
        have cast: (Nat.cast x.1) ^ 2 - (3: ℤ)  = Nat.cast (x.1 ^ 2 - 3) := by
         symm
         apply Int.natCast_sub
         calc
          3 ≤  2 * 2 := by omega
          _ ≤ x.1 * 2:= by omega
          _ ≤ x.1 * x.1 := by apply Nat.mul_le_mul_left;exact s
          _ = x.1 ^ 2 := by ring
        omega
    have x2_val: (x.2 = 1) ∨ (x.2 = 2) ∨ (x.2 = 3) := by omega
    rcases x2_val with d | d | d
    . rw [d] at h
      simp at h
      replace h: x.1 = 1 := by
        have o: x.1 < 2 := by
          by_contra! o
          have c: 2 ^ 2 ≤ 1 := by
            rw [← h]
            apply Nat.pow_le_pow_left
            exact o
          norm_num at c
        omega
      left
      calc
        x = (x.1,x.2) := by simp
         _= (1,1) := by rw[h];rw[d]
         _= 1 := by simp
    . rw [d] at h
      simp [id2] at h
      have o: x.1 < 2 := by
        by_contra! o
        replace o: 4 ≤ x.1 ^ 2 := by
          calc
            4 = 2 ^ 2 := by omega
            _ ≤ x.1 ^ 2 := by apply Nat.pow_le_pow_left; exact o
        rw [h] at o
        tauto
      have s: x.1 = 1 := by omega
      rw [s] at h
      tauto
    . rw [d] at h
      simp [id3] at h
      right
      replace h: x.1 = 3 := by
        nlinarith
      calc
        x = (x.1,x.2) := by simp
         _= (3,3) := by rw[h];rw[d]
  . simp
    intro hx
    rcases hx with hx | hx
    . rw [hx]
      simp
    . rw [hx]
      simp
      rw [id3]