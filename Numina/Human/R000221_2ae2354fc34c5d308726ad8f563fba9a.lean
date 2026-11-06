import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- Let  $a,b,c$  be positive integers such that  $a|b^3, b|c^3$  and  $c|a^3$ .
  Prove that  $abc|(a+b+c)^{13}$-/
theorem number_theory_8612
  (a b c : ℕ)
  (h₀ : 0 < a)
  (h₁ : 0 < b)
  (h₂ : 0 < c)
  (h₃ : a ∣ b^3)
  (h₄ : b ∣ c^3)
  (h₅ : c ∣ a^3) :
  a * b * c ∣ (a + b + c)^13 := by
    rw [add_pow]
    -- Auxiliary lemma : $a \mid c^9$.
    have hac : a ∣ c^9 := h₃.trans (by
      rw [show c^9 = (c^3)^3 by nlinarith]; exact pow_dvd_pow_of_dvd h₄ 3)
    -- Auxiliary lemma : $b \mid a^9$.
    have hba : b ∣ a^9 := h₄.trans (by
      rw [show a^9 = (a^3)^3 by nlinarith]; exact pow_dvd_pow_of_dvd h₅ 3)
    -- Auxiliary lemma : $c \mid b^9$.
    have hcb : c ∣ b^9 := h₅.trans (by
      rw [show b^9 = (b^3)^3 by nlinarith]; exact pow_dvd_pow_of_dvd h₃ 3)
    -- lets notice that all the elements in  $(a+b+c)^{13}$  are in the form of
    -- $(a+b)^ic^{13-i}$ , we will show that every one of them is divisible by abc
    apply Finset.dvd_sum
    intro i hi
    apply dvd_mul_of_dvd_left
    -- Case 1 : $i = 13$
    by_cases i13 : i = 13
    · simp [i13]
      -- all the elements in  $(a+b)^{13}$  are in the form of $a^jb^{13-j}$, we will show
      --  that every one of them is divisible by abc
      rw [add_pow]
      apply Finset.dvd_sum
      intro j hj
      -- Case 1.1 : $i = 13$ and $j = 0$
      by_cases j0 : j = 0
      · simp [j0]
        rw [show b^13 = b^4 * b^9 by nlinarith]
        refine mul_dvd_mul ?_ hcb
        refine mul_dvd_mul h₃ (Nat.dvd_refl b)
      · -- Case 1.2 : $i = 13$ and $j < 4$
        by_cases j4 : j < 4
        · apply dvd_mul_of_dvd_left
          rw [mul_assoc]
          refine mul_dvd_mul (by exact dvd_pow_self a j0) ?_
          have c1 : 10 ≤ 13 - j := by omega
          have c2 : b * c ∣ b^10 := by
            rw [show b^10 = b * b^9 by nlinarith]
            exact mul_dvd_mul (dvd_refl b) hcb
          exact c2.trans (by exact Nat.pow_dvd_pow b c1)
        · -- Case 1.2 : $i = 13$, $j = 13$.
          by_cases j13 : j = 13
          · simp [j13]
            have c1 : b * c ∣ a^12 := by
              rw [show a^12 = a^9 * a^3 by nlinarith]
              exact mul_dvd_mul hba h₅
            rw [mul_assoc, show a^13 = a * a^12 by nlinarith]
            exact mul_dvd_mul (dvd_refl a) c1
          · -- Case 1.3 : $i = 13$, $4 \leq j$ and $j \ne 13$.
            have c1 : a * c ∣ a ^j := by
              have : a * c ∣ a^4 := by
                rw [show a^4 = a * a^3 by nlinarith]
                exact mul_dvd_mul (dvd_refl a) h₅
              exact this.trans (by refine Nat.pow_dvd_pow a (by omega))
            · rw [show a * b * c = a * c * b by ring]
              apply dvd_mul_of_dvd_left
              exact mul_dvd_mul c1 (by refine dvd_pow_self b (by
                have : j ≤ 13 := by have := Finset.mem_range.1 hj; linarith
                omega))
    · by_cases ilt3 : i < 3
      · -- Case 2 : $i < 3$.
        interval_cases i <;> simp
        · have c1 : a * b ∣ c^12 := by
            rw [show c^12 = c^9 * c^3 by nlinarith]
            exact mul_dvd_mul hac h₄
          convert mul_dvd_mul c1 (dvd_refl c) using 1
        · ring_nf
          refine Nat.dvd_add ?_ ?_
          rw [mul_assoc]
          exact mul_dvd_mul (dvd_refl a) ((show b * c ∣c^4 by exact mul_dvd_mul h₄ (dvd_refl c)).trans (by
            refine Nat.pow_dvd_pow c (by simp) ))
          rw [mul_comm a b, mul_assoc]
          exact mul_dvd_mul (dvd_refl b) ((show a * c ∣ c^10 by exact mul_dvd_mul hac (dvd_refl c)).trans (by
            refine Nat.pow_dvd_pow c (by simp)))
        · ring_nf
          rw [add_assoc]
          refine Nat.dvd_add ?_ ?_
          calc
            _ ∣ a * b * c * (c^10 * 2) := Nat.dvd_mul_right (a * b * c) (c ^ 10 * 2)
            _ = _  := by ring
          apply Nat.dvd_add
          · rw [mul_assoc]
            refine mul_dvd_mul (dvd_pow_self a (by omega)) ?_
            exact (show b * c ∣ c^4 from mul_dvd_mul h₄ (dvd_refl c)).trans (by
              refine Nat.pow_dvd_pow c (by omega))
          · rw [mul_comm a b, mul_assoc]
            refine mul_dvd_mul (dvd_pow_self b (by omega)) ?_
            exact (show a * c ∣ c^10 by exact mul_dvd_mul hac (dvd_refl c)).trans (by
              refine Nat.pow_dvd_pow c (by omega))
      · by_cases ile9 : i ≤ 9
        -- Case 3 : $3 \leq i \leq 9$.
        · have c1 : a ∣ (a + b)^ i := by
            have : 3 ≤ i := by omega
            rw [add_pow]
            apply Finset.dvd_sum
            intro j _
            by_cases j0 : j = 0
            · simp [j0]; exact h₃.trans (by exact Nat.pow_dvd_pow b this)
            · apply dvd_mul_of_dvd_left
              apply dvd_mul_of_dvd_left
              exact dvd_pow_self a j0
          have c2 : b * c ∣ c ^ (13 - i) := by
            have : 4 ≤ 13 - i := by omega
            have c3 : b * c ∣ c^4 := mul_dvd_mul h₄ (dvd_refl c)
            exact c3.trans (by exact Nat.pow_dvd_pow c this)
          rw [mul_assoc]
          exact mul_dvd_mul c1 c2
        · -- Case 4 : $10 \leq i$.
          have ige10: 10 ≤ i := by omega
          have : i < 14 := Finset.mem_range.1 hi
          have c1 : a * b ∣ (a + b)^i := by
            rw [add_pow]
            apply Finset.dvd_sum
            intro j hj
            apply dvd_mul_of_dvd_left
            by_cases j0 : j = 0
            · simp [j0]
              have c1 : a * b ∣ b ^ 4 := mul_dvd_mul h₃ (dvd_refl b)
              exact c1.trans (by refine Nat.pow_dvd_pow b (by omega))
            · by_cases jeqi : j = i
              · simp [jeqi]
                have c1 : a * b ∣ a^10 := by
                  rw [show a^10 = a * a^9 by nlinarith]
                  exact mul_dvd_mul (dvd_refl a) hba
                exact c1.trans (by exact Nat.pow_dvd_pow a ige10)
              · have : j < i + 1 := Finset.mem_range.1 hj
                exact mul_dvd_mul (dvd_pow_self a j0) (dvd_pow_self b (by omega))
          exact mul_dvd_mul c1 (by refine dvd_pow_self c (by omega))
