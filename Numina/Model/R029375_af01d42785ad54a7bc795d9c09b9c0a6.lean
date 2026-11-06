import Mathlib

lemma pow_to_div (a b n : ℕ) (ha : a>0) (hb : b>0) (hn : n≠0) (h : a^(n+1) = b^n) : a = (b/a)^n ∧ b = (b/a)^(n+1) := by {
  /-First, we show that a is a divisor of b-/
  have anbn : a^n ∣ b^n := by {
    rw [←h]
    apply Nat.pow_dvd_pow
    simp
  }
  have div : Dvd.dvd a b := by {
  rw [←Nat.pow_dvd_pow_iff]
  exact anbn
  exact hn
  }
  /-Next, we show that a and b are powers of c=b/a-/
  let c : ℕ := b/a
  have ac : a*c = b := by {
     unfold c
     rw [Nat.mul_div_cancel']
     exact div
  }
  have acn : (a^n) * a = a^n * c^n := by { calc
  _ = a^(n+1) := by rw [Nat.pow_succ]
  _ = b^n := by rw [h]
  _ = (a*c)^n := by rw [←ac]
  _ = a^n * c^n := by rw [Nat.mul_pow]
  }
  have a_pow_g_zero : 0 < a^n := by { exact Nat.pos_pow_of_pos n ha }
  have a_pow_c : a = c^n := by {
    exact Nat.eq_of_mul_eq_mul_left a_pow_g_zero acn
  }
  have bcn : (b^n) * b = b^n * c^(n+1) := by { calc
  _ = b^(n+1) := by rw [Nat.pow_succ]
  _ = (a*c)^(n+1) := by rw [←ac]
  _ = a^(n+1) * c^(n+1) := by rw [Nat.mul_pow]
  _ = b^n * c^(n+1) := by rw [←h]
  }
  have b_pow_g_zero : 0 < b^n := by { exact Nat.pos_pow_of_pos n hb }
  have b_pow_c : b = c^(n+1) := by {
    exact Nat.eq_of_mul_eq_mul_left b_pow_g_zero bcn
  }
  apply And.intro
  exact a_pow_c
  exact b_pow_c
}

theorem number_theory_94838 (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
(h1 : a^5 = b^4) (h2 : c^3 = d^2) (h3 : c - a = 19) : d - b = 757 := by
  have four_not_zero : 4≠0 := by simp
  let s : ℕ := b/a
  have s_props : a = s^4 ∧ b = s^5 := pow_to_div a b 4 ha hb four_not_zero h1
  clear h1 four_not_zero
  obtain ⟨as, bs⟩ := s_props
  have two_not_zero : 2≠0 := by simp
  let t : ℕ := d/c
  have t_props : c = t^2 ∧ d = t^3 := pow_to_div c d 2 hc hd two_not_zero h2
  clear h2 two_not_zero
  obtain ⟨ct, dt⟩ := t_props
  /-So t^2−s^4=19.-/
  have h5 : t^2 - s^4 = 19 := by { calc
    _ = c - a := by rw[←ct,←as]
    _ = 19 := by rw[h3]
  }
  have t10 : t = 10 := by {
    /-We can factor the left-hand side of this equation as a difference of two squares, (t + s^2) * (t - s^2) = 19.-/
    have h4 : (t + s^2) * (t - s^2) = 19 := by { calc
      _ = t * t - (s^2) * (s^2) := by rw [←Nat.mul_self_sub_mul_self_eq]
      _ = t^2 - s^4 := by rw[←Nat.pow_add,←Nat.pow_two]
      _ = 19 := by rw [h5]
    }
    /-19 is a prime number-/
    have prime19 : Nat.Prime 19 := by norm_num
    have prime_prod : Nat.Prime ((t + s^2) * (t - s^2)) := by {
      rw [h4]
      exact prime19
    }
    /-so one of the factors t+s^2 or t-s^2 equals 1-/
    rw [Nat.prime_mul_iff] at prime_prod
    cases prime_prod
    case inl diff_1 := by {
      /-since t-s^2 is the smaller factor, it must be 1-/
      obtain ⟨_,diff_1'⟩ := diff_1
      have val_sum : t + s^2 = 19 := by { calc
        _ = (t + s^2) * 1 := by ring
        _ = (t + s^2) * (t - s^2) := by rw [←diff_1']
        _ = 19 := by rw [h4]
      }
      /-A calculation shows t=10-/
      have t_s2_g_0 : 0 < t - s^2 := by linarith
      have s2_leq_t' : 0 + s^2 < t := Nat.add_lt_of_lt_sub t_s2_g_0
      have s2_leq_t : s^2 ≤ t := by linarith
      have t20 : 2*10 = 2*t := by { calc
        _ = 1 + 19 := by arith_mult
        _ = (t - s^2) + (t + s^2) := by rw[←diff_1',←val_sum]
        _ = t - s^2 + s^2 + t := by ring
        _ = t + t := by rw[Nat.sub_add_cancel s2_leq_t]
        _ = 2*t := by ring
      }
      have le02 : 0 < 2 := by norm_num
      have t10' : 10 = t := Nat.eq_of_mul_eq_mul_left le02 t20
      rw [t10']
    }
    case inr sum_1 := by {
      /-since t+s^2 is the larger factor, it cannot be 1-/
      exfalso
      obtain ⟨_,sum_1'⟩ := sum_1
      have s2_neg : t + s^2 = 1 := by linarith
      have t_g_0 : 0 < t := by nlinarith [hc, ct]
      have s2_neg2 : s^2 ≤ t := by {
        linarith
      }
      nlinarith
    }
  }
  have s3 : s = 3 := by { 
    rw [t10] at h5
    have h6 : s^4 = 81 := by { 
      omega
    }
    have s3' : s = 3 := by {
      have h1 : s^4 = 81 := h6
      have h2 : s ≤ 3 := by {
        by_contra h
        push_neg at h
        have h3 : s ≥ 4 := by omega
        have h4 : s^4 ≥ 256 := by { 
          have : s ≥ 4 := h3
          have h5 : s^4 ≥ 4^4 := by
            apply Nat.pow_le_pow_of_le_left
            linarith
            all_goals linarith
          norm_num at h5 ⊢
          linarith
        }
        linarith
      }
      have h3 : s > 0 := by {
        by_contra h
        push_neg at h
        have h4 : s ≤ 0 := by omega
        have h5 : s^4 = 0 := by { 
          have h6 : s = 0 := by linarith
          rw [h6]
          all_goals linarith
        }
        linarith
      }
      have h4 : s < 4 := by omega
      interval_cases s <;> omega
    }
    exact s3'
  }
  have a81 : a = 81 := by { 
    rw [as]
    calc
      _ = 3^4 := by rw [s3]
      _ = 81 := by norm_num
  }
  have b243 : b = 243 := by { 
    rw [bs]
    calc
      _ = 3^5 := by rw [s3]
      _ = 243 := by norm_num
  }
  have c100 : c = 100 := by { 
    rw [ct]
    calc
      _ = 10^2 := by rw [t10]
      _ = 100 := by norm_num
  }
  have d1000 : d = 1000 := by { 
    rw [dt]
    calc
      _ = 10^3 := by rw [t10]
      _ = 1000 := by norm_num
  }
  calc 
    d - b = 1000 - 243 := by rw [d1000, b243]
    _ = 757 := by omega