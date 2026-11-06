import Mathlib

/- Bepaal alle paren $(x, y)$ van positieve gehele getallen die voldoen aan
$$
x+y+1 \mid 2 x y \quad \text { en } \quad x+y-1 \mid x^{2}+y^{2}-1
$$ -/

namespace NumberTheory_604916

lemma Int.gcd_add_self_right : ∀ (m n : ℤ), gcd m (n + m) = gcd m n := by
    intro m n
    simp [gcd]; simp [Int.gcd]
    match m with
    | Int.ofNat m =>
        match n with
        | Int.ofNat n =>
            have hmn : (Int.ofNat n + Int.ofNat m).natAbs = (Int.ofNat n).natAbs + (Int.ofNat m).natAbs := by
                apply Int.natAbs_add_of_nonneg; simp; simp
            simp at hmn; simp; rw [hmn]; apply Nat.gcd_add_self_right
        | Int.negSucc n =>
            simp
            by_cases hmn : m ≤ n
            have temp1 : (Int.negSucc n + (m : ℤ)).natAbs = n + 1 - m := by
                have k_ex : ∃ k : ℕ, n = m + k := by apply Nat.exists_eq_add_of_le hmn
                obtain ⟨k, hk⟩ := k_ex
                rw [Int.negSucc_eq, hk, add_assoc]; nth_rw 4 [add_comm]; simp; ring_nf; rw [← Int.natAbs_neg]
                ring_nf; apply Int.ofNat_inj.1; rw [Int.natAbs_of_nonneg];simp; linarith [k]
            have temp2 : m ≤ n + 1 := by linarith [hmn]
            rw [temp1]
            calc
                m.gcd (n + 1 - m) = m.gcd (n + 1 - m + m) := by rw [eq_comm]; apply Nat.gcd_add_self_right
                _ = m.gcd (n + 1) := by simp [temp2]
            simp at hmn
            have temp1 : (Int.negSucc n + (m : ℤ)).natAbs = m - (n + 1) := by
                have k_ex : ∃ k : ℕ, m = n + 1 + k := by apply Nat.exists_eq_add_of_le hmn
                obtain ⟨k, hk⟩ := k_ex
                rw [Int.negSucc_eq, hk]; simp; ring_nf; simp
            rw [temp1]; apply Nat.gcd_self_sub_right; linarith [hmn]
    | Int.negSucc m =>
        match n with
        | Int.ofNat n =>
            simp
            by_cases hmn : n ≤ m
            have temp1 : ((n : ℤ) + Int.negSucc m).natAbs = m + 1 - n := by
                have k_ex : ∃ k : ℕ, m = n + k := by apply Nat.exists_eq_add_of_le hmn
                obtain ⟨k, hk⟩ := k_ex
                rw [Int.negSucc_eq, hk, add_assoc]; nth_rw 4 [add_comm]; simp; ring_nf; rw [← Int.natAbs_neg]
                ring_nf; apply Int.ofNat_inj.1; rw [Int.natAbs_of_nonneg];simp; linarith [k]
            rw [temp1]; apply Nat.gcd_self_sub_right; linarith [hmn]
            simp at hmn
            have temp1 : ((n : ℤ) + Int.negSucc m).natAbs = n - (m + 1) := by
                have k_ex : ∃ k : ℕ, n = m + 1 + k := by apply Nat.exists_eq_add_of_le hmn
                obtain ⟨k, hk⟩ := k_ex
                rw [Int.negSucc_eq, hk]; simp; ring_nf; simp
            rw [temp1]
            have temp2 : n ≥ m + 1 := by linarith [hmn]
            calc
                (m + 1).gcd (n - (m + 1)) = (m + 1).gcd (n - (m + 1) + (m + 1)) := by rw [eq_comm]; apply Nat.gcd_add_self_right
                _ = (m + 1).gcd n := by simp [temp2]
        | Int.negSucc n =>
            rw [Int.negSucc_eq, Int.negSucc_eq, Int.natAbs_neg, Int.natAbs_neg]; nth_rw 2 [← Int.natAbs_neg]; ring_nf
            calc
                (1 + (m : ℤ)).natAbs.gcd (2 + (m : ℤ) + (n : ℤ)).natAbs = (1 + (m : ℤ)).natAbs.gcd ((1 + (n : ℤ)).natAbs + (1 + (m : ℤ)).natAbs) := by
                    rw [← Int.natAbs_add_of_nonneg]; ring_nf; linarith [m]; linarith [n]
                _ = (1 + (m : ℤ)).natAbs.gcd (1 + (n : ℤ)).natAbs := by apply Nat.gcd_add_self_right


lemma Int.gcd_add_mul_self : ∀ (m n k : ℤ), gcd m (n + k * m) = gcd m n := by
    intro m n k
    match k with
    | Int.ofNat l =>
        induction l with
        | zero => simp
        | succ j hj =>
            simp; ring_nf; simp at hj
            calc
                gcd m (n + ↑j * m + m) = gcd m (n + ↑j * m) := by apply Int.gcd_add_self_right
                _ = gcd m n := by apply hj
    | Int.negSucc l =>
        induction l with
        | zero =>
            simp
            calc
                gcd m (n + -m) = gcd m (n + -m + m) := by rw [eq_comm]; apply Int.gcd_add_self_right
                _ = gcd m n := by simp
        | succ j hj =>
            rw [Int.negSucc_eq]; simp; ring_nf; rw [Int.negSucc_eq] at hj; simp at hj
            calc
                gcd m (n + (-((j : ℤ) * m) - m * 2)) = gcd m (n + (-((j : ℤ) * m) - m * 2) + m) := by rw [eq_comm]; apply Int.gcd_add_self_right
                _ = gcd m (n + (-1 + -(j : ℤ)) * m) := by ring_nf
                _ = gcd m n := by apply hj


lemma mul_dvd_both_dvd_mul_gcd :
        ∀ a b c : ℤ, a ∣ c → b ∣ c → a > 0 →
        (a * b) ∣ (c * gcd a b) := by
        intro a b c hac hbc ha
        let d := gcd a b
        have hd : d = gcd a b := rfl
        have d_pos : d > 0 := by simp [d, gcd]; apply Int.gcd_pos_iff.2; left; apply ne_of_gt; exact ha
        have d_ne_zero : d ≠ 0 := by apply ne_of_gt; exact d_pos
        have p_ex : ∃ p, a = p * d := by apply exists_eq_mul_left_of_dvd; simp [d]; apply Int.gcd_dvd_left
        have q_ex : ∃ q, b = q * d := by apply exists_eq_mul_left_of_dvd; simp [d]; apply Int.gcd_dvd_right
        obtain ⟨p, hp⟩ := p_ex
        obtain ⟨q, hq⟩ := q_ex
        have u_ex : ∃ u, c = u * a := by apply exists_eq_mul_left_of_dvd; exact hac
        have v_ex : ∃ v, c = v * b := by apply exists_eq_mul_left_of_dvd; exact hbc
        obtain ⟨u, hu⟩ := u_ex
        obtain ⟨v, hv⟩ := v_ex
        have hpq : gcd p q = 1 := by
            have temp : d = gcd a b := rfl
            rw [hp, hq] at temp; simp at temp
            have normalize_d : normalize d = d := by apply (Int.nonneg_iff_normalize_eq_self d).2; linarith [d_pos]
            rw [normalize_d] at temp
            calc
                gcd p q = (gcd p q) * d / d := by simp [d_ne_zero]
                _ = d / d := by rw [← temp]
                _ = 1 := by simp [d_ne_zero]
        have temp1 : p * u = q * v := by
            calc
                p * u = p * u * d / d := by simp [d_ne_zero]
                _ = q * v * d / d := by
                    have c_eq : p * u * d = q * v * d := by
                        calc
                            p * u * d = c := by rw [hu, hp]; ring
                            _ = q * v * d := by rw [hv, hq]; ring
                    rw [c_eq]
                _ = q * v := by simp [d_ne_zero]
        have temp2 : p ∣ (v * q) := by apply dvd_iff_exists_eq_mul_left.2; use u; rw [mul_comm, ← temp1, mul_comm]
        have hpv : p ∣ v * (gcd p q) := by apply dvd_mul_gcd_of_dvd_mul temp2
        rw [hpq] at hpv; simp at hpv
        rw [← hd, hp, hv, hq, mul_assoc, mul_assoc]
        let w := d * d * q
        have w_1 : d * (q * d) = w := by ring
        have w_2 : q * d * d = w := by ring
        rw [w_1, w_2]; apply mul_dvd_mul_right hpv

end NumberTheory_604916

open NumberTheory_604916

theorem NumberTheory_604916 (x y : ℤ) (hx : 0 < x) (hy : 0 < y) :
    (x + y + 1 ∣ 2 * x * y) ∧ (x + y - 1 ∣ x ^ 2 + y ^ 2 - 1) ↔
    (y = x + 1 ∧ 1 ≤ x) ∨ (y = x - 1 ∧ 2 ≤ x) := by

    apply Iff.intro
    ·   intro h0
        have h3 : x + y - 1 ∣ 2 * x * y := by
            have normalize_eq : normalize (x + y - 1) = x + y - 1 := by apply (Int.nonneg_iff_normalize_eq_self (x + y - 1)).2; linarith [hx, hy]
            apply (gcd_eq_left_iff (x + y - 1) (2 * x * y) normalize_eq).1
            calc
                gcd (x + y - 1) (2 * x * y) = gcd (x + y - 1) (-(x ^ 2 + y ^ 2 - 1) + (x + y + 1) * (x + y - 1)) := by ring_nf
                _ = gcd (x + y - 1) (-(x ^ 2 + y ^ 2 - 1)) := by apply Int.gcd_add_mul_self
                _ = gcd (x + y - 1) (x ^ 2 + y ^ 2 - 1) := by
                    simp [gcd, Int.gcd]; nth_rw 2 [← Int.natAbs_neg]; ring_nf
                _ = x + y - 1 := by apply (gcd_eq_left_iff (x + y - 1) (x ^ 2 + y ^ 2 - 1) normalize_eq).2 h0.2

        have dvd1 : (x + y + 1) * (x + y - 1) ∣ (2 * x * y) * (gcd (x + y + 1) (x + y - 1)) := by
            apply mul_dvd_both_dvd_mul_gcd; exact h0.1; exact h3; linarith [hx, hy]

        have dvd2 : gcd (x + y + 1) (x + y - 1) ∣ 2 := by
            have temp : gcd (x + y + 1) (x + y - 1) = gcd (x + y - 1) 2 := by
                calc
                    gcd (x + y + 1) (x + y - 1) = gcd (x + y - 1) (x + y + 1) := by rw [gcd_comm]
                    _ = gcd (x + y - 1) ((x + y + 1) + (-1) * (x + y - 1)) := by rw [eq_comm]; apply Int.gcd_add_mul_self
                    _ = gcd (x + y - 1) 2 := by ring_nf
            rw [temp]; apply Int.gcd_dvd_right

        have dvd3 : (x + y + 1) * (x + y - 1) ∣ 4 * x * y := by
            calc
                (x + y + 1) * (x + y - 1) ∣ (2 * x * y) * (gcd (x + y + 1) (x + y - 1)) := dvd1
                _ ∣ (2 * x * y) * 2 := by apply mul_dvd_mul_left; exact dvd2
                _ = 4 * x * y := by ring_nf

        have k_ex : ∃ k, 4 * x * y = k * ((x + y + 1) * (x + y - 1)) := by
            apply exists_eq_mul_left_of_dvd; exact dvd3
        obtain ⟨k, hk⟩ := k_ex
        have k_pos : k > 0 := by
            have pos1 : 4 * x * y > 0 := by
                apply mul_pos; linarith [hx]; linarith [hy]
            have pos2 : (x + y + 1) * (x + y - 1) > 0 := by
                apply mul_pos; linarith [hx, hy]; linarith [hx, hy]
            by_contra h
            simp at h
            have contr : 4 * x * y ≤ 0 := by
                calc
                    4 * x * y = k * ((x + y + 1) * (x + y - 1)) := hk
                    _ ≤ 0 := by nlinarith [h, pos2]
            linarith [pos1, contr]
        have iq1 : 4 * x * y ≥ k * (4 * x * y - 1) := by
            nth_rw 1 [hk]; apply (mul_le_mul_left k_pos).2
            calc
                4 * x * y - 1 = (x + y + 1) * (x + y - 1) - (x - y) ^ 2 := by ring_nf
                _ ≤ (x + y + 1) * (x + y - 1) := by linarith [pow_two_nonneg (x - y)]
        have k_eq_one : k = 1 := by
            by_contra h
            have hk' : k ≥ 2 := by
                match k with
                | Int.ofNat k =>
                    simp [Int.ofNat]; simp [Int.ofNat] at k_pos; simp [Int.ofNat] at h
                    apply Nat.le_of_lt_succ; simp
                    have temp : 1 < k := by apply lt_of_le_of_ne; linarith [k_pos]; simp; rw [eq_comm]; exact h
                    linarith [temp]
                | Int.negSucc k => rw [Int.negSucc_eq] at k_pos; linarith [k_pos]
            have iq2 : 4 * x * y ≥ 2 * (4 * x * y - 1) := by
                calc
                    4 * x * y ≥ k * (4 * x * y - 1) := by exact iq1
                    _ ≥ 2 * (4 * x * y - 1) := by
                        have pos : 4 * x * y - 1 > 0 := by nlinarith [hx, hy]
                        apply (mul_le_mul_right pos).2; exact hk'
            have contr : 4 * x * y ≤ 2 := by linarith [iq2]
            nlinarith [contr, hx, hy]
        rw [k_eq_one] at hk; ring_nf at hk
        have succ_or_prod : x - y - 1 = 0 ∨ x - y + 1 = 0 := by
            apply mul_eq_zero.1; linarith [hk]
        cases succ_or_prod with
        | inl hxy =>
            right; apply And.intro; linarith [hxy]
            have hxy' : x = y + 1 := by linarith [hxy]
            rw [hxy']; linarith [hy]
        | inr hxy =>
            left; apply And.intro; linarith [hxy]; linarith [hx]
    ·   intro hxy
        cases hxy with
        | inl hxy =>
            rw [hxy.1]; apply And.intro
            ring_nf
            have temp : x * 2 + x ^ 2 * 2 = (2 + x * 2) * x := by ring
            rw [temp]; apply dvd_mul_right
            ring_nf
            have temp : x * 2 + x ^ 2 * 2 = (x * 2) * (x + 1) := by ring
            rw [temp]; apply dvd_mul_right
        | inr hxy =>
            rw [hxy.1]; apply And.intro
            ring_nf
            have temp : -(x * 2) + x ^ 2 * 2 = (x * 2) * (x - 1) := by ring
            rw [temp]; apply dvd_mul_right
            ring_nf
            have temp : -(x * 2) + x ^ 2 * 2 = (-2 + x * 2) * x := by ring
            rw [temp]; apply dvd_mul_right
