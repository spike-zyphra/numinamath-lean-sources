import Mathlib

set_option maxHeartbeats 400000

open Nat

/-
6. (8) Which natural numbers can be represented in the form $[x, y]+[y, z]+[z, x]$ with natural $x, y, z$? $[a, b]$ is the least common multiple of numbers $a$ and $b$.

保留了源文本的换行和格式。
 -/
theorem number_theory_119261 (n : ℕ) : (∃ x > 0, ∃ y > 0, ∃ z > 0, n = x.lcm y + y.lcm z + z.lcm x) ↔ n > 0 ∧ n ∉ Set.range (2 ^ .) := by
  -- 6. Ответ: Все, кроме степеней 2 .
  -- The reference solution
  --simp
  symm
  constructor
  . rintro ⟨n_pos, n_not_in_range_2_pow_p⟩
    -- Во-первых рассмотрим число, не являющееся степенью двойки, $n=2^{p}(2 q+1), q>0$.
    have := Nat.exists_eq_pow_mul_and_not_dvd (n := n) (by omega) 2 (by simp)
    rcases this with ⟨p, e, _2_ndvd_e, n_eq_2_pow_p_mul⟩
    have e_mod_2_eq_1 : e % 2 = 1 := by
      omega
    have _2_q_add_1_eq_e := Nat.div_add_mod e 2
    set q := e / 2
    rw [e_mod_2_eq_1] at _2_q_add_1_eq_e
    rw [←_2_q_add_1_eq_e] at n_eq_2_pow_p_mul
    have q_pos : q > 0 := by
      by_contra q_ne_0
      simp at q_ne_0
      simp [q_ne_0] at n_eq_2_pow_p_mul
      exact n_not_in_range_2_pow_p ⟨p, n_eq_2_pow_p_mul.symm⟩
    -- Имеем $n=2^{p}+2^{p} q+2^{p} q=$ $\left[1,2^{p}\right]+\left[1,2^{p} q\right]+\left[2^{p}, 2^{p} q\right]$.
    have : 2 ^ p > 0 := by
      simp
    use 1, by simp, 2 ^ p, this, 2 ^ p * q, by nlinarith
    simp
    have : (2 ^ p).lcm (2 ^ p * q) = 2 ^ p * q := by
      have : 2 ^ p ∣ 2 ^ p * q := by
        exact Nat.dvd_mul_right (2 ^ p) q
      rw [←lcm_eq_nat_lcm]
      have := (lcm_eq_right_iff (2 ^ p) (2 ^ p * q) (by simp)).mpr this
      exact this
    rw [this]
    rw [n_eq_2_pow_p_mul]
    ring
  . intro ex_n_eq_lcm_sum
    rcases ex_n_eq_lcm_sum with ⟨x, x_pos, y, y_pos, z, z_pos, n_eq_lcm_sum⟩
    constructor
    . rw [n_eq_lcm_sum]
      have : x.lcm y > 0 := by
        exact lcm_pos x_pos y_pos
      linarith
    . -- Теперь докажем, что степень 2 не представить в таком виде. Если $x=2^{a} u, y=2^{b} v, z=2^{c} w$, $a \leqslant b \leqslant c, u, v, w$ нечетны, то $[x, y]+[y, z]+[z, x]=2^{b}\left([u, v]+2^{c-b}([v, w]+[u, w])\right)$.
      have := Nat.exists_eq_pow_mul_and_not_dvd (n := x) (by linarith) 2 (by simp)
      rcases this with ⟨a, h_x_a⟩
      have := Nat.exists_eq_pow_mul_and_not_dvd (n := y) (by linarith) 2 (by simp)
      rcases this with ⟨b, h_y_b⟩
      have := Nat.exists_eq_pow_mul_and_not_dvd (n := z) (by linarith) 2 (by simp)
      rcases this with ⟨c, h_z_c⟩
      let H x a := ∃ u, ¬2 ∣ u ∧ x = 2 ^ a * u
      -- The `wlog` tactic works poorly here so I introduce a `wlog` function.
      have wlog :
          ∀ x > 0, ∀ y > 0, ∀ z > 0,
          n = x.lcm y + y.lcm z + z.lcm x →
          ∀ a, H x a → ∀ b, H y b → ∀ c, H z c →
          a ≤ b → b ≤ c →
          n ∉ Set.range fun x ↦ 2 ^ x := by
        intro x x_pos y y_pos z z_pos n_eq_lcm_sum a h_x_a b h_y_b c h_z_c a_le_b b_le_c
        rcases h_x_a with ⟨u, _2_ndvd_u, x_eq⟩
        rcases h_y_b with ⟨v, _2_ndvd_v, y_eq⟩
        rcases h_z_c with ⟨w, _2_ndvd_w, z_eq⟩
        have u_pos : u > 0 := by
          omega
        have v_pos : v > 0 := by
          omega
        have w_pos : w > 0 := by
          omega
        have prime_2 := Nat.prime_two
        rw [x_eq, y_eq, z_eq] at n_eq_lcm_sum
        have n_eq : n = 2 ^ b * (u.lcm v + 2 ^ (c - b) * (v.lcm w + u.lcm w)) := by
          convert n_eq_lcm_sum using 1
          have simp_lcm a b u (u_pos : u > 0) v (a_le_b : a ≤ b) (_2_ndvd_u : ¬2 ∣ u) (_2_ndvd_v : ¬2 ∣ v) : (2 ^ a * u).lcm (2 ^ b * v) = 2 ^ b * u.lcm v := by
            let d := b - a
            have : 2 ^ b = 2 ^ a * 2 ^ d := by
              rw [show b = a + d by omega]
              ring
            rw [this]
            have : (2 ^ a * u).lcm (2 ^ a * 2 ^ d * v) = 2 ^ a * u.lcm (2 ^ d * v) := by
              rw [show 2 ^ a * 2 ^ d * v = 2 ^ a * (2 ^ d * v) by ring]
              exact Nat.lcm_mul_left
            rw [this]
            have : u.lcm (2 ^ d * v) = 2 ^ d * u.lcm v := by
              have : /- u.Coprime (2 ^ d) -/ (2 ^ d).Coprime u := by
                refine Coprime.pow_left d ?_
                exact (Nat.Prime.coprime_iff_not_dvd prime_2).mpr _2_ndvd_u
              let gcd := u.gcd v
              have gcd_mul_lcm_eq : gcd * u.lcm (2 ^ d * v) = gcd * (2 ^ d * u.lcm v) := by
                unfold gcd
                have : u.gcd (2 ^ d * v) = u.gcd v := by
                  exact Coprime.gcd_mul_left_cancel_right v this
                conv_lhs => rw [←this]
                -- strangely, not found from LeanSearch
                have := Nat.gcd_mul_lcm u (2 ^ d * v)
                rw [this]
                have := Nat.gcd_mul_lcm u v
                rw [show u * (2 ^ d * v) = 2 ^ d * (u * v) by ring]
                rw [←this]
                ring
              have gcd_pos : gcd > 0 := by
                unfold gcd
                exact Nat.gcd_pos_of_pos_left v u_pos
              --nlinarith
              exact Nat.eq_of_mul_eq_mul_left gcd_pos gcd_mul_lcm_eq
            rw [this]
            ring
          have := simp_lcm a b u u_pos v a_le_b _2_ndvd_u _2_ndvd_v
          rw [this]
          have := simp_lcm b c v v_pos w b_le_c _2_ndvd_v _2_ndvd_w
          rw [this]
          have := simp_lcm a c u u_pos w (by linarith) _2_ndvd_u _2_ndvd_w
          rw [Nat.lcm_comm (2 ^ a * u) (2 ^ c * w)] at this
          rw [this]
          conv_rhs => rw [show c = b + (c - b) by omega]
          ring
        -- Выражение в скобках нечетно и больше 1 , так что все произведение не может быть степенью 2 .
        intro n_eq_2_pow
        simp at n_eq_2_pow
        rcases n_eq_2_pow with ⟨d, _2_pow_d_eq_n⟩
        set n' := u.lcm v + 2 ^ (c - b) * (v.lcm w + u.lcm w)
        have : n' > 1 := by
          unfold n'
          have : u.lcm v > 0 := by
            exact lcm_pos u_pos v_pos
          /- have : u.lcm v ≥ 1 := by
            linarith -/
          have : v.lcm w > 0 := by
            exact lcm_pos v_pos w_pos
          /- have : v.lcm w ≥ 1 := by
            linarith -/
          have : 2 ^ (c - b) > 0 := by
            simp
          nlinarith
        have : ¬ 2 ∣ n' := by
          unfold n'
          have lcm_odd {u : ℕ} (_2_ndvd_u : ¬ 2 ∣ u) {v : ℕ} (_2_ndvd_v : ¬ 2 ∣ v) : ¬ 2 ∣ u.lcm v := by
            intro _2_dvd_lcm
            have : 2 ∣ u ∨ 2 ∣ v := by
              have := Nat.gcd_mul_lcm u v
              have : 2 ∣ u * v := by
                rw [←this]
                exact Dvd.dvd.mul_left _2_dvd_lcm (u.gcd v)
              exact (Nat.Prime.dvd_mul prime_2).mp this
            omega
          have : ¬ 2 ∣ u.lcm v :=
            lcm_odd _2_ndvd_u _2_ndvd_v
          have : 2 ∣ 2 ^ (c - b) * (v.lcm w + u.lcm w) := by
            have : 2 ∣ v.lcm w + u.lcm w := by
              have := lcm_odd _2_ndvd_v _2_ndvd_w
              have := lcm_odd _2_ndvd_u _2_ndvd_w
              omega
            exact Dvd.dvd.mul_left this (2 ^ (c - b))
          omega
        have _2_pow_eq : 2 ^ d = 2 ^ b * n' := by
          linarith
        have : d > b := by
          have : 2 ^ d > 2 ^ b := by
            nlinarith
          exact (Nat.pow_lt_pow_iff_right (by simp)).mp this
        have : 2 ∣ n' := by
          have : 2 ^ b * 2 ^ (d - b) = 2 ^ b * n' := by
            convert _2_pow_eq using 1
            conv_rhs => rw [show d = b + (d - b) by omega]
            ring
          have : 2 ^ (d - b) = n' := by
            --nlinarith
            exact Nat.eq_of_mul_eq_mul_left (by simp) this
          rw [←this]
          apply dvd_pow (by simp) (by omega)
        contradiction
      have : x.lcm y = y.lcm x := by
        exact Nat.lcm_comm x y
      have := Nat.lcm_comm y z
      have := Nat.lcm_comm z x
      by_cases a_le_b : a ≤ b
      . by_cases b_le_c : b ≤ c
        . --exact?
          exact wlog x x_pos y y_pos z z_pos n_eq_lcm_sum a h_x_a b h_y_b c h_z_c a_le_b b_le_c
        . have c_le_b : c ≤ b := by linarith
          by_cases a_le_c : a ≤ c
          . exact wlog x x_pos z z_pos y y_pos (by linarith) a h_x_a c h_z_c b h_y_b a_le_c c_le_b
          . have c_le_a : c ≤ a := by linarith
            exact wlog z z_pos x x_pos y y_pos (by linarith) c h_z_c a h_x_a b h_y_b c_le_a a_le_b
      . have b_le_a : b ≤ a := by linarith
        by_cases a_le_c : a ≤ c
        . exact wlog y y_pos x x_pos z z_pos (by linarith) b h_y_b a h_x_a c h_z_c b_le_a a_le_c
        . have c_le_a : c ≤ a := by linarith
          by_cases b_le_c : b ≤ c
          . exact wlog y y_pos z z_pos x x_pos (by linarith) b h_y_b c h_z_c a h_x_a b_le_c c_le_a
          . have c_le_b : c ≤ b := by linarith
            exact wlog z z_pos y y_pos x x_pos (by linarith) c h_z_c b h_y_b a h_x_a c_le_b b_le_a
