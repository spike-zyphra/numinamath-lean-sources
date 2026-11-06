import Mathlib

/- Find all positive integers $a, b, c$ and $p$, where $p$ is a prime number, such that

$$
73 p^{2}+6=9 a^{2}+17 b^{2}+17 c^{2}
$$ -/
theorem number_theory_604288: {(a,b,c,p): ℕ × ℕ × ℕ × ℕ | (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (0 < p) ∧
(Nat.Prime p) ∧ (73 * p^2 + 6 = 9 * a^2 + 17 * b^2 + 17 * c^2)} = {(1,1,4,2),(1,4,1,2)} := by
  have mod8: ∀ x: ℕ, x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by  -- x ^ 2 mod 8 = 0, 1, 4 --
    intro x
    let y:= x % 8
    have hy: x % 8 = y := by rfl
    have eq: x ^ 2 % 8 = y ^ 2 % 8 := by
      calc
        x ^ 2 % 8 = (x % 8) ^ 2 % 8 := by apply Nat.pow_mod
                 _= y ^ 2 % 8 := by simp [y]
    rw [eq]
    have cy: y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 := by omega
    clear eq hy
    clear_value y
    -- enumerate all cases for y --
    rcases cy with i | i | i | i | i | i | i | i
    . simp [i]
    . simp [i]
    . simp [i]
    . simp [i]
    . simp [i]
    . simp [i]
    . simp [i]
    . simp [i]
  have mod8_2: ∀ x: ℕ, x % 2 = 1 → x ^ 2 % 8 = 1 := by -- x ^ 2 mod 8 = 1 for odd x --
    intro x hx
    have h1: x ^ 2 % 8 ≠ 0 := by
      by_contra! o
      apply Nat.dvd_of_mod_eq_zero at o
      replace o: 4 ∣ x ^ 2 := by omega
      rw [show 4 = 2 ^ 2 by rfl] at o
      rw [Nat.pow_dvd_pow_iff] at o
      . omega
      . norm_num
    have h2: x ^ 2 % 8 ≠ 4 := by
      by_contra! o
      replace o: 4 ∣ x ^ 2 % 8 := by omega
      rw [Nat.dvd_mod_iff] at o
      replace o: 4 ∣ x ^ 2 := by omega
      rw [show 4 = 2 ^ 2 by rfl] at o
      rw [Nat.pow_dvd_pow_iff] at o
      . omega
      . norm_num
      norm_num
    specialize mod8 x
    omega
  ext ⟨a, b, c, p⟩
  constructor

  -- the forward direction --
  . intro h
    simp at h
    simp
    rcases h with ⟨ha,hb,hc,hp,prime_p,h⟩
    replace hp: 2 ≤ p := by
      by_contra! o
      replace o: p = 1 := by omega
      rw [o] at prime_p
      absurd prime_p
      norm_num
    by_cases l: 3 ≤ p
    -- case 1: p ≥ 3, then p is odd --
    . have p_mod2: p % 2 = 1 := by
        have o:= Nat.Prime.eq_two_or_odd prime_p
        omega
      specialize mod8_2 p p_mod2
      have left_mod8: (73 * p ^ 2 + 6) % 8 = 7 := by
        have eq: p ^ 2 * 73 % 8 = (p ^ 2 % 8) * 73 % 8 := by
          symm
          apply Nat.mod_mul_mod
        rw [mod8_2] at eq
        calc
            (73 * p ^ 2 + 6) % 8 = ((73 * p ^ 2 % 8) + (6 % 8)) % 8 := by apply Nat.add_mod
                                _= ((73 * p ^ 2 % 8) + 6) % 8 := by norm_num
                                _=  (p ^ 2 * 73 % 8 + 6) % 8 := by rw [show 73 * p ^ 2 =  p ^ 2 * 73 by ring]
                                _=  (1 * 73 % 8 + 6) % 8 := by rw [eq]
                                _= 7 := by norm_num
      have right_mod8: (9 * a ^ 2 + 17 * b ^ 2 + 17 * c ^ 2) % 8 = ((a ^ 2 % 8) + (b ^ 2 % 8) + (c ^ 2 % 8)) % 8 := by
        have eqa: (9 * a ^ 2) % 8 = a ^ 2 % 8 := by
          calc
            (9 * a ^ 2) % 8 = 9 % 8 * a ^ 2 % 8 := by rw [Nat.mod_mul_mod]
                          _ = a ^ 2 % 8 := by norm_num
        have eqb: (17 * b ^ 2) % 8 = b ^ 2 % 8 := by
          calc
            (17 * b ^ 2) % 8 = 17 % 8 * b ^ 2 % 8 := by rw [Nat.mod_mul_mod]
                          _ = b ^ 2 % 8 := by norm_num
        have eqc: (17 * c ^ 2) % 8 = c ^ 2 % 8 := by
          calc
            (17 * c ^ 2) % 8 = 17 % 8 * c ^ 2 % 8 := by rw [Nat.mod_mul_mod]
                          _ = c ^ 2 % 8 := by norm_num
        calc
          (9 * a ^ 2 + 17 * b ^ 2 + 17 * c ^ 2) % 8 = ((9 * a ^ 2) % 8 + (17 * b ^ 2) % 8  + (17 * c ^ 2) % 8) % 8 := by simp [Nat.add_mod]
                                                  _ = ((a ^ 2 % 8) + (b ^ 2 % 8) + (c ^ 2 % 8)) % 8 := by rw[eqa];rw[eqb];rw[eqc]
      replace h: (73 * p ^ 2 + 6) % 8= (9 * a ^ 2 + 17 * b ^ 2 + 17 * c ^ 2) % 8 := by simp [h]
      rw [left_mod8] at h
      rw [right_mod8] at h
      symm at h
      absurd h
      clear *- mod8
      have moda:= mod8 a
      have modb:= mod8 b
      have modc:= mod8 c
      let x:= a ^ 2 % 8
      let y:= b ^ 2 % 8
      let z:= c ^ 2 % 8
      have hx: a ^ 2 % 8 = x := by rfl
      have hy: b ^ 2 % 8 = y := by rfl
      have hz: c ^ 2 % 8 = z := by rfl
      rw [hx] at moda
      rw [hy] at modb
      rw [hz] at modc
      simp [hx, hy, hz]
      clear hx hy hz mod8
      clear_value x y z
      -- enumerate all cases --
      rcases moda with moda | moda | moda
      . simp [moda] at *
        rcases modb with modb | modb | modb
        . simp [modb] at *
          rcases modc with modc | modc | modc
          . simp [modc] at *
          . simp [modc] at *
          . simp [modc] at *
        . simp [modb] at *
          rcases modc with modc | modc | modc
          . simp [modc] at *
          . simp [modc] at *
          . simp [modc] at *
        . simp [modb] at *
          rcases modc with modc | modc | modc
          . simp [modc] at *
          . simp [modc] at *
          . simp [modc] at *
      . simp [moda] at *
        rcases modb with modb | modb | modb
        . simp [modb] at *
          rcases modc with modc | modc | modc
          . simp [modc] at *
          . simp [modc] at *
          . simp [modc] at *
        . simp [modb] at *
          rcases modc with modc | modc | modc
          . simp [modc] at *
          . simp [modc] at *
          . simp [modc] at *
        . simp [modb] at *
          rcases modc with modc | modc | modc
          . simp [modc] at *
          . simp [modc] at *
          . simp [modc] at *
      . simp [moda] at *
        rcases modb with modb | modb | modb
        . simp [modb] at *
          rcases modc with modc | modc | modc
          . simp [modc] at *
          . simp [modc] at *
          . simp [modc] at *
        . simp [modb] at *
          rcases modc with modc | modc | modc
          . simp [modc] at *
          . simp [modc] at *
          . simp [modc] at *
        . simp [modb] at *
          rcases modc with modc | modc | modc
          . simp [modc] at *
          . simp [modc] at *
          . simp [modc] at *
    -- case 2: p = 2 --
    . replace l: p = 2 := by omega
      simp [l] at *
      clear hp l prime_p mod8 mod8_2
      have ineq: b ^ 2 + c ^ 2 ≤ 17 := by nlinarith
      by_cases o: c ≤ b
      -- case 1: c ≤ b --
      . have j: c ≤ 2 := by nlinarith
        replace j: c = 1 ∨ c = 2 := by omega
        rcases j with j | j
        . simp [j] at *
          clear j o hc
          replace ineq: b ≤ 4 := by nlinarith
          replace ineq: b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by omega
          rcases ineq with ineq | ineq | ineq | ineq
          . simp [ineq] at h
            omega
          . simp [ineq] at h
            omega
          . simp [ineq] at h
            omega
          . simp [ineq] at h
            simp [ineq]
            have l: a < 2 := by
              by_contra! no
              have s: 2 ^ 2 ≤ 1 := by
                rw [← h]
                apply Nat.pow_le_pow_left
                exact no
              norm_num at s
            omega
        . simp [j] at *
          clear j o hc
          replace ineq: b ≤ 3 := by nlinarith
          replace ineq: b = 1 ∨ b = 2 ∨ b = 3 := by omega
          rcases ineq with ineq | ineq | ineq
          . simp [ineq] at h
            omega
          . simp [ineq] at h
            replace h: a ^ 2 = 18 := by omega
            have f: a < 5 := by nlinarith
            have g: a > 5 := by nlinarith
            omega
          . simp [ineq] at h
            omega
      -- case 2: c > b --
      . have j: b ≤ 2 := by nlinarith
        replace j: b = 1 ∨ b = 2 := by omega
        rcases j with j | j
        . simp [j] at *
          clear j o hb
          replace ineq: c ≤ 4 := by nlinarith
          replace ineq: c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega
          rcases ineq with ineq | ineq | ineq | ineq
          . simp [ineq] at h
            omega
          . simp [ineq] at h
            omega
          . simp [ineq] at h
            omega
          . simp [ineq] at h
            simp [ineq]
            have l: a < 2 := by
              by_contra! no
              have s: 2 ^ 2 ≤ 1 := by
                rw [← h]
                apply Nat.pow_le_pow_left
                exact no
              norm_num at s
            omega
        . simp [j] at *
          clear j o hb
          replace ineq: c ≤ 3 := by nlinarith
          replace ineq: c = 1 ∨ c = 2 ∨ c = 3 := by omega
          rcases ineq with ineq | ineq | ineq
          . simp [ineq] at h
            omega
          . simp [ineq] at h
            replace h: a ^ 2 = 18 := by omega
            have f: a < 5 := by nlinarith
            have g: a > 5 := by nlinarith
            omega
          . simp [ineq] at h
            omega

  -- the backward direction --
  . intro h
    simp at h
    clear mod8 mod8_2
    simp
    rcases h with h | h
    . simp [h]
      norm_num
    . simp [h]
      norm_num