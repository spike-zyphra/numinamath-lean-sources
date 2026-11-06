import Mathlib

open Finset Real Nat
/- John is older than Mary. He notices that if he switches the two digits of his age (an integer), he gets Mary's age.
Moreover, the difference between the squares of their ages is the square of an integer.
How old are Mary and John? -/
theorem number_theory_241506 {j m : ℤ} (ineq : j > m) (hjm : m = 10 * (j % 10) + (j / 10)) (hj: 0 ≤ j) (hm: 0 ≤ m) (hj2: j ≤ 99) (hm2: m ≤ 99)
    (hdiff : ∃ k, k^2 = j^2 - m^2) :
    j = 65 ∧ m = 56 := by
    let b:= j % 10
    let a:= j / 10
    have eqj: j = 10 * a + b := by
        simp [a,b]
        omega
    have eqm: m = 10 * b + a := by
        simp [a,b]
        omega
    have ineq_ab: a > b := by
        by_contra! ab
        have contra: j ≤ m := by
            rw [eqj, eqm]
            omega
        omega
    have ineqa: a ≤ 9 := by
        omega
    have ineqb: b ≤ 9 := by
        omega
    clear_value a b
    obtain ⟨k, hk⟩ := hdiff
    simp [eqj, eqm] at hk
    have id: (10 * a + b) ^ 2 - (10 * b + a) ^ 2 = 9 * 11 * (a + b) * (a - b) := by
        ring_nf
    rw [id] at hk
    have dvd11_k: 11 ∣ k ^ 2 := by
        rw [hk]
        rw [ show 9 * 11 * (a + b) * (a - b) = 11 * (9 * (a + b) * (a - b)) by ring]
        apply Int.dvd_mul_right
    replace dvd11_k: 11 ∣ k := by
         have prime_11: Nat.Prime 11 := by norm_num
         apply Prime.dvd_of_dvd_pow at dvd11_k
         exact dvd11_k
         simp [prime_11]
    have dvd121: 11 * 11 ∣ k ^ 2 := by
        rw [show k ^ 2 = k * k by ring]
        have o: 11 * 11 ∣ 11 * k := by
            apply Int.mul_dvd_mul_left 11 at dvd11_k
            exact dvd11_k
        have v: 11 * k ∣ k * k := by
            apply Int.mul_dvd_mul_right k at dvd11_k
            exact dvd11_k
        apply Int.dvd_trans o v
    rw [hk] at dvd121
    rw [show 9 * 11 * (a + b) * (a - b) = 11 * (9 * (a + b) * (a - b)) by ring] at dvd121
    apply Int.dvd_of_mul_dvd_mul_left at dvd121
    rw [show 9 * (a + b) * (a - b)= 9 * ((a + b) * (a - b)) by ring] at dvd121
    replace dvd121: 11 ∣ (a + b) * (a - b) := by
        apply Int.dvd_of_dvd_mul_right_of_gcd_one at dvd121
        have gcd11_9: Int.gcd 11 9 = 1 := by
            norm_num
        simp [gcd11_9] at dvd121
        exact dvd121
    apply Int.Prime.dvd_mul' at dvd121
    simp at dvd121
    apply exists_eq_mul_right_of_dvd at dvd11_k
    obtain ⟨c, hc⟩ := dvd11_k
    rw [hc] at hk
    rcases dvd121 with dvd11_1 | dvd11_2
    . have ab: a + b ≤ 18 := by
        omega
      replace dvd_11_1: a + b = 11 := by omega
      rw [dvd_11_1] at hk
      have hc: c ^ 2 = 9 * (a - b) := by
        ring_nf at hk
        rw [show a * 1089 - b * 1089 = 9 * (a - b) * 121 by ring] at hk
        apply Int.eq_of_mul_eq_mul_right at hk
        exact hk
        omega
      let x:= a - b
      have hx1: 1 ≤ x := by omega
      have hx2: x ≤ 9 := by omega
      have x_val: (x = 1) ∨ (x = 4) ∨ (x = 9):= by
        by_contra! ne
        replace hx1: 2 ≤ x := by omega
        replace hc: c ^ 2 = 9 * x := by omega
        clear_value x
        clear * - hx1 hx2 hc ne
        have h : 3^2 ∣ c^2 := by rw [hc]; exact ⟨x, rfl⟩
        rw [sq] at h
        have h3c : 3 ∣ c ^ 2 := by
            omega
        have h3: 3 ∣ c := by
            have prime_3: Nat.Prime 3 := by norm_num
            apply Prime.dvd_of_dvd_pow at h3c
            exact h3c
            simp [prime_3]
        apply exists_eq_mul_right_of_dvd at h3
        obtain ⟨d, hd⟩ := h3
        rw [hd] at hc
        replace hc: d ^ 2 = x := by
            rw [show (3 * d) ^ 2 = 9 * d ^ 2 by ring] at hc
            apply Int.eq_of_mul_eq_mul_left at hc
            exact hc
            omega
        let e:= abs d
        have e1: 0 ≤ e := by
            simp [e]
        have he: e ^ 2 = x := by
            simp [e]
            exact hc
        have e1: e ≤ 3 := by
            by_contra! e1
            have contra: x > 9 := by
                rw [← hc]
                nlinarith
            omega
        have d_ne: e ≠ 0 := by
            by_contra! e0
            rw [e0] at he
            simp at he
            omega
        have e_val: (e = 1) ∨ (e = 2) ∨ (e = 3) := by
            omega
        rcases e_val with e1 | e2 | e3
        . rw [e1] at he
          omega
        . rw [e2] at he
          omega
        . rw [e3] at he
          omega
      rcases x_val with x1 | x2 | x3
      . simp [x] at x1
        omega
      . simp [x] at x2
        omega
      . simp [x] at x3
        omega
    . apply exists_eq_mul_right_of_dvd at dvd11_2
      have i1: a - b > 0 := by omega
      have i2: a - b ≤ 9 := by omega
      obtain ⟨c, hc⟩ := dvd11_2
      have c1: 0 < c := by omega
      have c2: c < 1 := by omega
      omega
    norm_num
    omega
