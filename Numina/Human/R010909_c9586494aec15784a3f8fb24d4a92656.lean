import Mathlib
/-It is given that $\log_{6}a + \log_{6}b + \log_{6}c = 6$, where $a$, $b$, and $c$ are positive integers that form an increasing geometric sequence and $b - a$ is the square of an integer. Find $a + b + c$.-/
theorem algebra_22534

    (a b c : ℕ) (r : ℤ)

    (h₀ : 0 < a)

    (h₁ : 0 < b)

    (h₂ : 0 < c)

    (h₃ : b - a = m^2)

    (h₄ :  (b :ℝ) = a * r ∧ (c :ℝ ) = b * r)

    (h₅ : Real.logb 6 a + Real.logb 6 b + Real.logb 6 c = 6)

    (h₆ : a < b ∧  b < c)

    (h₇ : (c : ℝ) = b * b / a →   (b * b) % a = 0):

    a + b + c = 111 := by
    rw [← Real.logb_mul] at h₅; rw [← Real.logb_mul] at h₅
    rcases h₄ with ⟨hb,hc⟩
    rcases h₆ with ⟨hgb,hgc⟩
    have  ha :  0 < (a: ℝ) := by
      norm_cast
    have  hbl :  0 < (b: ℝ) := by
      norm_cast
    have hcl :  0 < (c: ℝ) := by
      norm_cast
    have hab  : (0 : ℝ) <  a * b := by
      apply Left.mul_pos ha hbl
    have heq : (0:ℝ ) < ↑a * ↑b * ↑c  := by
      apply Left.mul_pos hab hcl
    --By the properties of logarithms, \[\log_6 a +\log_6 b+\log_6c = \log_6(abc) = 6,\]so $abc = 6^6.$ But $(a, b, c)$ is an increasing geometric sequence, so $ac = b^2,$ and $abc = b^3 = 6^6.$ Thus, $b = 6^2 = 36.$
    have h : (6 : ℝ ) ^ Real.logb 6 (↑a * ↑b * ↑c) = (↑a * ↑b * ↑c):= by
      rw[Real.rpow_logb]
      linarith
      linarith
      exact heq
    rw [h₅] at h
    symm at h
    have  hb2 : (↑b : ℝ) * b = a * c  := by
      rw [hc]; rw [hb]
      norm_cast
      ring_nf
    have h7 := congrArg ( fun (n) => ((n) / (a : ℝ  )) ) hb2; beta_reduce at h7 ;
    rw [show ↑a * ↑c / ↑a = (c : ℝ) * (a / a) by ring_nf] at h7
    rw [div_self] at h7; simp at h7; symm at h7
    have hd :=  h₇ (h7)
    rw [show ↑a * ↑b * (↑c : ℝ)= a * c * b by ring_nf] at h
    rw [← hb2] at h
    rw [show (↑b : ℝ) * b * b = b ^ 3 by ring_nf] at h
    rw [show  (6 : ℝ) ^ (6 : ℝ) =  6 ^ (6 : ℕ) by norm_num] at h
    rw [show  (6 : ℝ) ^ 6 = (6 ^ 2) ^ 3 by ring_nf] at h
    rw [pow_eq_pow_iff_cases] at h
    have  hn :  3 % 2 = 1 := by simp
    rw [← Nat.not_even_iff] at hn
    have  hn2 : Even 3 = False := by
      norm_num
      rw [Odd]
      use 1
      ring_nf
    rw [hn2] at h
    simp at h
    norm_cast at h
    have  hm : 0 < b - a  := by
      rw[tsub_pos_iff_lt]
      exact hgb
    rw [h₃] at hm
    rw [h] at h₃
    have hm2 :  6 ^ 2 - a < 6 ^ 2 := by
      apply tsub_lt_self
      linarith
      exact h₀
    rw [h₃] at hm2
    rw [← Nat.sqrt_lt'] at hm2
    rw [Nat.sqrt_eq'] at hm2
    rw [← Nat.sqrt_lt'] at hm
    rw [Nat.sqrt_zero] at hm
    have heq2 :  b = m ^ 2 + a := by
      apply Nat.eq_add_of_sub_eq
      linarith
      rw [h]
      exact h₃
    rw [h] at heq2
    have hr := congrArg ( fun (n) => ((n) / (a : ℝ  )) ) hb; beta_reduce at hr
    rw [show (a : ℝ) * r / ↑a = a / a * r  by ring_nf] at hr
    rw [div_self] at hr; simp at hr; rw [h] at hr
    have e := congrArg ( fun (n) => ((n) - m ^ 2) ) heq2; beta_reduce at e
    rw [h] at hd; ring_nf at hd
    --Therefore $b-a=36 - a$ is a nonzero perfect square. We also have $c = b^2/a = 6^4/a,$ so $a$ must be a divisor of $6^4.$ Testing perfect square values for $36-a,$ we find that the only possible value of $a$ is $a = 27,$ giving $c = 6^4/27 = 48.$ Thus, \[a+b+c = 27+36+48=\boxed{111}.\]
    rw [← Finset.mem_range] at hm2
    fin_cases hm2
    tauto
    simp at e; rw [← e] at hd; ring_nf at hd
    tauto
    simp at e; rw [← e] at hd; ring_nf at hd
    tauto
    simp at e; rw [← e] at hd; ring_nf at hd
    rw [← e] at hr; rw [h] at hc; rw [← hr] at hc; ring_nf at hc
    norm_cast at hc
    rw [← e];rw [h];rw [hc]; ring_nf
    simp at e; rw [← e] at hd; ring_nf at hd
    tauto
    simp at e; rw [← e] at hd; ring_nf at hd
    tauto
    linarith
    linarith
    simp; constructor
    linarith
    linarith
    norm_cast; linarith
    norm_cast; linarith
    norm_cast; linarith
    